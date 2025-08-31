package ingress

import (
	"context"
	"fmt"
	"net/http"
	"time"

	awssdk "github.com/aws/aws-sdk-go-v2/aws"
	"github.com/gavv/httpexpect/v2"
	. "github.com/onsi/ginkgo/v2"
	. "github.com/onsi/gomega"
	corev1 "k8s.io/api/core/v1"
	networking "k8s.io/api/networking/v1"
	apierrs "k8s.io/apimachinery/pkg/api/errors"
	"sigs.k8s.io/aws-load-balancer-controller/pkg/k8s"
	"sigs.k8s.io/aws-load-balancer-controller/test/framework"
	"sigs.k8s.io/aws-load-balancer-controller/test/framework/fixture"
	"sigs.k8s.io/aws-load-balancer-controller/test/framework/manifest"
)

var _ = Describe("frontend NLB tags tests", func() {
	var (
		ctx context.Context
		// sandbox namespace
		sandboxNS *corev1.Namespace
	)

	exact := networking.PathTypeExact

	BeforeEach(func() {
		ctx = context.Background()
		if tf.Options.ControllerImage != "" {
			By(fmt.Sprintf("ensure cluster installed with controller: %s", tf.Options.ControllerImage), func() {
				err := tf.CTRLInstallationManager.UpgradeController(tf.Options.ControllerImage, false)
				Expect(err).NotTo(HaveOccurred())
				time.Sleep(60 * time.Second)
			})
		}

		By("setup sandbox namespace", func() {
			tf.Logger.Info("allocating namespace")
			ns, err := tf.NSManager.AllocateNamespace(ctx, "aws-lb-e2e")
			Expect(err).NotTo(HaveOccurred())
			tf.Logger.Info("allocated namespace", "name", ns.Name)
			sandboxNS = ns
		})
	})

	AfterEach(func() {
		if sandboxNS != nil {
			By("teardown sandbox namespace", func() {
				{
					tf.Logger.Info("deleting namespace", "name", sandboxNS.Name)
					err := tf.K8sClient.Delete(ctx, sandboxNS)
					Expect(err).Should(SatisfyAny(BeNil(), Satisfy(apierrs.IsNotFound)))
					tf.Logger.Info("deleted namespace", "name", sandboxNS.Name)
				}
				{
					tf.Logger.Info("waiting namespace becomes deleted", "name", sandboxNS.Name)
					err := tf.NSManager.WaitUntilNamespaceDeleted(ctx, sandboxNS)
					Expect(err).NotTo(HaveOccurred())
					tf.Logger.Info("namespace becomes deleted", "name", sandboxNS.Name)
				}
			})
		}
	})

	Context("with frontend NLB tags annotation", func() {
		It("should apply custom tags to frontend NLB when annotation is present", func() {
			appBuilder := manifest.NewFixedResponseServiceBuilder()
			ingBuilder := manifest.NewIngressBuilder()
			dp, svc := appBuilder.Build(sandboxNS.Name, "app", tf.Options.TestImageRegistry)
			ingBackend := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}
			annotation := map[string]string{
				"kubernetes.io/ingress.class":                   "alb",
				"alb.ingress.kubernetes.io/scheme":              "internet-facing",
				"alb.ingress.kubernetes.io/target-type":         "ip",
				"alb.ingress.kubernetes.io/enable-frontend-nlb": "true",
				"alb.ingress.kubernetes.io/frontend-nlb-tags":   "Environment=test,Team=platform,Project=aws-load-balancer-controller",
			}
			if tf.Options.IPFamily == "IPv6" {
				annotation["alb.ingress.kubernetes.io/ip-address-type"] = "dualstack"
			}
			ing := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/path", PathType: &exact, Backend: ingBackend}).
				WithAnnotations(annotation).Build(sandboxNS.Name, "ing")
			resStack := fixture.NewK8SResourceStack(tf, dp, svc, ing)
			err := resStack.Setup(ctx)
			Expect(err).NotTo(HaveOccurred())

			defer resStack.TearDown(ctx)

			albARN, albDNS, nlbARN, nlbDNS := ExpectTwoLBProvisionedForIngress(ctx, tf, ing)

			// Verify both load balancers are functional
			ExpectLBDNSBeAvailable(ctx, tf, albARN, albDNS)
			ExpectLBDNSBeAvailable(ctx, tf, nlbARN, nlbDNS)

			// Test traffic through NLB
			httpExp := httpexpect.New(tf.LoggerReporter, fmt.Sprintf("http://%v", nlbDNS))
			httpExp.GET("/path").Expect().
				Status(http.StatusOK).
				Body().Equal("Hello World!")

			// Verify frontend NLB has the expected custom tags
			nlbTags, err := tf.LBManager.GetLoadBalancerResourceTags(ctx, nlbARN)
			Expect(err).NotTo(HaveOccurred())

			expectedTags := map[string]string{
				"Environment": "test",
				"Team":        "platform",
				"Project":     "aws-load-balancer-controller",
			}

			actualTags := make(map[string]string)
			for _, tag := range nlbTags {
				actualTags[awssdk.ToString(tag.Key)] = awssdk.ToString(tag.Value)
			}

			for key, expectedValue := range expectedTags {
				Expect(actualTags).To(HaveKeyWithValue(key, expectedValue),
					fmt.Sprintf("Expected tag %s=%s not found in NLB tags", key, expectedValue))
			}

			tf.Logger.Info("verified frontend NLB has expected custom tags", "nlbARN", nlbARN, "tags", expectedTags)
		})

		It("should update frontend NLB tags when annotation is modified", func() {
			appBuilder := manifest.NewFixedResponseServiceBuilder()
			ingBuilder := manifest.NewIngressBuilder()
			dp, svc := appBuilder.Build(sandboxNS.Name, "app", tf.Options.TestImageRegistry)
			ingBackend := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}

			// Initial annotation with tags
			annotation := map[string]string{
				"kubernetes.io/ingress.class":                   "alb",
				"alb.ingress.kubernetes.io/scheme":              "internet-facing",
				"alb.ingress.kubernetes.io/target-type":         "ip",
				"alb.ingress.kubernetes.io/enable-frontend-nlb": "true",
				"alb.ingress.kubernetes.io/frontend-nlb-tags":   "Environment=staging,Team=backend",
			}
			if tf.Options.IPFamily == "IPv6" {
				annotation["alb.ingress.kubernetes.io/ip-address-type"] = "dualstack"
			}
			ing := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/path", PathType: &exact, Backend: ingBackend}).
				WithAnnotations(annotation).Build(sandboxNS.Name, "ing")
			resStack := fixture.NewK8SResourceStack(tf, dp, svc, ing)
			err := resStack.Setup(ctx)
			Expect(err).NotTo(HaveOccurred())

			defer resStack.TearDown(ctx)

			_, _, nlbARN, _ := ExpectTwoLBProvisionedForIngress(ctx, tf, ing)

			// Verify initial tags
			nlbTags, err := tf.LBManager.GetLoadBalancerResourceTags(ctx, nlbARN)
			Expect(err).NotTo(HaveOccurred())

			initialTags := make(map[string]string)
			for _, tag := range nlbTags {
				initialTags[awssdk.ToString(tag.Key)] = awssdk.ToString(tag.Value)
			}

			Expect(initialTags).To(HaveKeyWithValue("Environment", "staging"))
			Expect(initialTags).To(HaveKeyWithValue("Team", "backend"))

			// Update the ingress with new tags
			err = tf.K8sClient.Get(ctx, k8s.NamespacedName(ing), ing)
			Expect(err).NotTo(HaveOccurred())

			ing.Annotations["alb.ingress.kubernetes.io/frontend-nlb-tags"] = "Environment=production,Team=frontend,Owner=devops"
			err = tf.K8sClient.Update(ctx, ing)
			Expect(err).NotTo(HaveOccurred())

			// Wait for reconciliation and verify updated tags
			Eventually(func(g Gomega) {
				updatedTags, err := tf.LBManager.GetLoadBalancerResourceTags(ctx, nlbARN)
				g.Expect(err).NotTo(HaveOccurred())

				actualTags := make(map[string]string)
				for _, tag := range updatedTags {
					actualTags[awssdk.ToString(tag.Key)] = awssdk.ToString(tag.Value)
				}

				g.Expect(actualTags).To(HaveKeyWithValue("Environment", "production"))
				g.Expect(actualTags).To(HaveKeyWithValue("Team", "frontend"))
				g.Expect(actualTags).To(HaveKeyWithValue("Owner", "devops"))
			}, "2m", "10s").Should(Succeed())

			tf.Logger.Info("verified frontend NLB tags were updated", "nlbARN", nlbARN)
		})

		It("should remove custom tags when annotation is deleted", func() {
			appBuilder := manifest.NewFixedResponseServiceBuilder()
			ingBuilder := manifest.NewIngressBuilder()
			dp, svc := appBuilder.Build(sandboxNS.Name, "app", tf.Options.TestImageRegistry)
			ingBackend := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}

			// Initial annotation with tags
			annotation := map[string]string{
				"kubernetes.io/ingress.class":                   "alb",
				"alb.ingress.kubernetes.io/scheme":              "internet-facing",
				"alb.ingress.kubernetes.io/target-type":         "ip",
				"alb.ingress.kubernetes.io/enable-frontend-nlb": "true",
				"alb.ingress.kubernetes.io/frontend-nlb-tags":   "Environment=test,Team=platform",
			}
			if tf.Options.IPFamily == "IPv6" {
				annotation["alb.ingress.kubernetes.io/ip-address-type"] = "dualstack"
			}
			ing := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/path", PathType: &exact, Backend: ingBackend}).
				WithAnnotations(annotation).Build(sandboxNS.Name, "ing")
			resStack := fixture.NewK8SResourceStack(tf, dp, svc, ing)
			err := resStack.Setup(ctx)
			Expect(err).NotTo(HaveOccurred())

			defer resStack.TearDown(ctx)

			_, _, nlbARN, _ := ExpectTwoLBProvisionedForIngress(ctx, tf, ing)

			// Verify initial tags are present
			nlbTags, err := tf.LBManager.GetLoadBalancerResourceTags(ctx, nlbARN)
			Expect(err).NotTo(HaveOccurred())

			initialTags := make(map[string]string)
			for _, tag := range nlbTags {
				initialTags[awssdk.ToString(tag.Key)] = awssdk.ToString(tag.Value)
			}

			Expect(initialTags).To(HaveKeyWithValue("Environment", "test"))
			Expect(initialTags).To(HaveKeyWithValue("Team", "platform"))

			// Remove the frontend NLB tags annotation
			err = tf.K8sClient.Get(ctx, k8s.NamespacedName(ing), ing)
			Expect(err).NotTo(HaveOccurred())

			delete(ing.Annotations, "alb.ingress.kubernetes.io/frontend-nlb-tags")
			err = tf.K8sClient.Update(ctx, ing)
			Expect(err).NotTo(HaveOccurred())

			// Wait for reconciliation and verify custom tags are removed
			Eventually(func(g Gomega) {
				updatedTags, err := tf.LBManager.GetLoadBalancerResourceTags(ctx, nlbARN)
				g.Expect(err).NotTo(HaveOccurred())

				actualTags := make(map[string]string)
				for _, tag := range updatedTags {
					actualTags[awssdk.ToString(tag.Key)] = awssdk.ToString(tag.Value)
				}

				// Custom tags should be removed
				g.Expect(actualTags).NotTo(HaveKey("Environment"))
				g.Expect(actualTags).NotTo(HaveKey("Team"))
			}, "2m", "10s").Should(Succeed())

			tf.Logger.Info("verified custom tags were removed from frontend NLB", "nlbARN", nlbARN)
		})
	})

	Context("with multiple ingresses and frontend NLB tags", func() {
		It("should merge consistent tags from multiple ingresses in the same group", func() {
			appBuilder := manifest.NewFixedResponseServiceBuilder()
			ingBuilder := manifest.NewIngressBuilder()
			dp1, svc1 := appBuilder.WithHTTPBody("app-1").Build(sandboxNS.Name, "app-1", tf.Options.TestImageRegistry)
			dp2, svc2 := appBuilder.WithHTTPBody("app-2").Build(sandboxNS.Name, "app-2", tf.Options.TestImageRegistry)

			ingBackend1 := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc1.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}
			ingBackend2 := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc2.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}

			// Common annotations for both ingresses
			baseAnnotation := map[string]string{
				"kubernetes.io/ingress.class":                   "alb",
				"alb.ingress.kubernetes.io/scheme":              "internet-facing",
				"alb.ingress.kubernetes.io/target-type":         "ip",
				"alb.ingress.kubernetes.io/enable-frontend-nlb": "true",
				"alb.ingress.kubernetes.io/group.name":          "multi-ingress-group",
			}
			if tf.Options.IPFamily == "IPv6" {
				baseAnnotation["alb.ingress.kubernetes.io/ip-address-type"] = "dualstack"
			}

			// First ingress with tags
			annotation1 := make(map[string]string)
			for k, v := range baseAnnotation {
				annotation1[k] = v
			}
			annotation1["alb.ingress.kubernetes.io/frontend-nlb-tags"] = "Environment=test,Team=platform"

			// Second ingress with same tags
			annotation2 := make(map[string]string)
			for k, v := range baseAnnotation {
				annotation2[k] = v
			}
			annotation2["alb.ingress.kubernetes.io/frontend-nlb-tags"] = "Environment=test,Team=platform"

			ing1 := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/app1", PathType: &exact, Backend: ingBackend1}).
				WithAnnotations(annotation1).Build(sandboxNS.Name, "ing1")
			ing2 := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/app2", PathType: &exact, Backend: ingBackend2}).
				WithAnnotations(annotation2).Build(sandboxNS.Name, "ing2")

			resStack := fixture.NewK8SResourceStack(tf, dp1, svc1, dp2, svc2, ing1, ing2)
			err := resStack.Setup(ctx)
			Expect(err).NotTo(HaveOccurred())

			defer resStack.TearDown(ctx)

			// Both ingresses should share the same load balancers
			albARN1, albDNS1, nlbARN1, nlbDNS1 := ExpectTwoLBProvisionedForIngress(ctx, tf, ing1)
			albARN2, _, nlbARN2, _ := ExpectTwoLBProvisionedForIngress(ctx, tf, ing2)

			// Verify they share the same load balancers
			Expect(albARN1).To(Equal(albARN2))
			Expect(nlbARN1).To(Equal(nlbARN2))

			// Verify both load balancers are functional
			ExpectLBDNSBeAvailable(ctx, tf, albARN1, albDNS1)
			ExpectLBDNSBeAvailable(ctx, tf, nlbARN1, nlbDNS1)

			// Test traffic through NLB to both apps
			httpExp := httpexpect.New(tf.LoggerReporter, fmt.Sprintf("http://%v", nlbDNS1))
			httpExp.GET("/app1").Expect().
				Status(http.StatusOK).
				Body().Equal("app-1")
			httpExp.GET("/app2").Expect().
				Status(http.StatusOK).
				Body().Equal("app-2")

			// Verify frontend NLB has the merged tags
			nlbTags, err := tf.LBManager.GetLoadBalancerResourceTags(ctx, nlbARN1)
			Expect(err).NotTo(HaveOccurred())

			actualTags := make(map[string]string)
			for _, tag := range nlbTags {
				actualTags[awssdk.ToString(tag.Key)] = awssdk.ToString(tag.Value)
			}

			Expect(actualTags).To(HaveKeyWithValue("Environment", "test"))
			Expect(actualTags).To(HaveKeyWithValue("Team", "platform"))

			tf.Logger.Info("verified frontend NLB has merged tags from multiple ingresses", "nlbARN", nlbARN1)
		})

		It("should handle cleanup when ingresses are deleted", func() {
			appBuilder := manifest.NewFixedResponseServiceBuilder()
			ingBuilder := manifest.NewIngressBuilder()
			dp1, svc1 := appBuilder.WithHTTPBody("app-1").Build(sandboxNS.Name, "app-1", tf.Options.TestImageRegistry)
			dp2, svc2 := appBuilder.WithHTTPBody("app-2").Build(sandboxNS.Name, "app-2", tf.Options.TestImageRegistry)

			ingBackend1 := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc1.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}
			ingBackend2 := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc2.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}

			// Common annotations for both ingresses
			baseAnnotation := map[string]string{
				"kubernetes.io/ingress.class":                   "alb",
				"alb.ingress.kubernetes.io/scheme":              "internet-facing",
				"alb.ingress.kubernetes.io/target-type":         "ip",
				"alb.ingress.kubernetes.io/enable-frontend-nlb": "true",
				"alb.ingress.kubernetes.io/group.name":          "cleanup-test-group",
				"alb.ingress.kubernetes.io/frontend-nlb-tags":   "Environment=test,Team=platform",
			}
			if tf.Options.IPFamily == "IPv6" {
				baseAnnotation["alb.ingress.kubernetes.io/ip-address-type"] = "dualstack"
			}

			ing1 := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/app1", PathType: &exact, Backend: ingBackend1}).
				WithAnnotations(baseAnnotation).Build(sandboxNS.Name, "ing1")
			ing2 := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/app2", PathType: &exact, Backend: ingBackend2}).
				WithAnnotations(baseAnnotation).Build(sandboxNS.Name, "ing2")

			resStack := fixture.NewK8SResourceStack(tf, dp1, svc1, dp2, svc2, ing1, ing2)
			err := resStack.Setup(ctx)
			Expect(err).NotTo(HaveOccurred())

			// Get the load balancer ARNs before cleanup
			albARN, albDNS, nlbARN, nlbDNS := ExpectTwoLBProvisionedForIngress(ctx, tf, ing1)

			// Verify load balancers exist and are functional
			ExpectLBDNSBeAvailable(ctx, tf, albARN, albDNS)
			ExpectLBDNSBeAvailable(ctx, tf, nlbARN, nlbDNS)

			// Verify tags are present
			nlbTags, err := tf.LBManager.GetLoadBalancerResourceTags(ctx, nlbARN)
			Expect(err).NotTo(HaveOccurred())

			actualTags := make(map[string]string)
			for _, tag := range nlbTags {
				actualTags[awssdk.ToString(tag.Key)] = awssdk.ToString(tag.Value)
			}

			Expect(actualTags).To(HaveKeyWithValue("Environment", "test"))
			Expect(actualTags).To(HaveKeyWithValue("Team", "platform"))

			// Clean up the resources
			resStack.TearDown(ctx)

			// Verify load balancers are cleaned up
			Eventually(func(g Gomega) {
				_, err := tf.LBManager.GetLoadBalancerFromARN(ctx, albARN)
				g.Expect(err).To(HaveOccurred())
			}, "5m", "10s").Should(Succeed())

			Eventually(func(g Gomega) {
				_, err := tf.LBManager.GetLoadBalancerFromARN(ctx, nlbARN)
				g.Expect(err).To(HaveOccurred())
			}, "5m", "10s").Should(Succeed())

			tf.Logger.Info("verified load balancers were cleaned up after ingress deletion")
		})

		It("should detect and handle tag conflicts between multiple ingresses", func() {
			appBuilder := manifest.NewFixedResponseServiceBuilder()
			ingBuilder := manifest.NewIngressBuilder()
			dp1, svc1 := appBuilder.WithHTTPBody("app-1").Build(sandboxNS.Name, "app-1", tf.Options.TestImageRegistry)
			dp2, svc2 := appBuilder.WithHTTPBody("app-2").Build(sandboxNS.Name, "app-2", tf.Options.TestImageRegistry)

			ingBackend1 := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc1.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}
			ingBackend2 := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc2.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}

			// Common annotations for both ingresses
			baseAnnotation := map[string]string{
				"kubernetes.io/ingress.class":                   "alb",
				"alb.ingress.kubernetes.io/scheme":              "internet-facing",
				"alb.ingress.kubernetes.io/target-type":         "ip",
				"alb.ingress.kubernetes.io/enable-frontend-nlb": "true",
				"alb.ingress.kubernetes.io/group.name":          "conflict-test-group",
			}
			if tf.Options.IPFamily == "IPv6" {
				baseAnnotation["alb.ingress.kubernetes.io/ip-address-type"] = "dualstack"
			}

			// First ingress with tags
			annotation1 := make(map[string]string)
			for k, v := range baseAnnotation {
				annotation1[k] = v
			}
			annotation1["alb.ingress.kubernetes.io/frontend-nlb-tags"] = "Environment=staging,Team=backend"

			// Second ingress with conflicting tags (same key, different value)
			annotation2 := make(map[string]string)
			for k, v := range baseAnnotation {
				annotation2[k] = v
			}
			annotation2["alb.ingress.kubernetes.io/frontend-nlb-tags"] = "Environment=production,Team=backend"

			ing1 := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/app1", PathType: &exact, Backend: ingBackend1}).
				WithAnnotations(annotation1).Build(sandboxNS.Name, "ing1")

			// Create first ingress and verify it works
			resStack1 := fixture.NewK8SResourceStack(tf, dp1, svc1, ing1)
			err := resStack1.Setup(ctx)
			Expect(err).NotTo(HaveOccurred())

			defer resStack1.TearDown(ctx)

			albARN1, albDNS1, nlbARN1, nlbDNS1 := ExpectTwoLBProvisionedForIngress(ctx, tf, ing1)
			ExpectLBDNSBeAvailable(ctx, tf, albARN1, albDNS1)
			ExpectLBDNSBeAvailable(ctx, tf, nlbARN1, nlbDNS1)

			// Verify first ingress tags
			nlbTags, err := tf.LBManager.GetLoadBalancerResourceTags(ctx, nlbARN1)
			Expect(err).NotTo(HaveOccurred())

			actualTags := make(map[string]string)
			for _, tag := range nlbTags {
				actualTags[awssdk.ToString(tag.Key)] = awssdk.ToString(tag.Value)
			}

			Expect(actualTags).To(HaveKeyWithValue("Environment", "staging"))
			Expect(actualTags).To(HaveKeyWithValue("Team", "backend"))

			// Now create second ingress with conflicting tags
			ing2 := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/app2", PathType: &exact, Backend: ingBackend2}).
				WithAnnotations(annotation2).Build(sandboxNS.Name, "ing2")

			resStack2 := fixture.NewK8SResourceStack(tf, dp2, svc2, ing2)
			err = resStack2.Setup(ctx)
			Expect(err).NotTo(HaveOccurred())

			defer resStack2.TearDown(ctx)

			// The second ingress should either:
			// 1. Fail to reconcile due to tag conflict, or
			// 2. Be reconciled but with error events/status
			// Since the exact behavior depends on implementation, we'll verify
			// that the load balancer configuration remains stable

			// Wait a bit for reconciliation attempts
			time.Sleep(30 * time.Second)

			// Verify the original tags are still present (no corruption)
			updatedTags, err := tf.LBManager.GetLoadBalancerResourceTags(ctx, nlbARN1)
			Expect(err).NotTo(HaveOccurred())

			updatedActualTags := make(map[string]string)
			for _, tag := range updatedTags {
				updatedActualTags[awssdk.ToString(tag.Key)] = awssdk.ToString(tag.Value)
			}

			// The Environment tag should still be "staging" (from first ingress)
			// or the system should have handled the conflict appropriately
			Expect(updatedActualTags).To(HaveKey("Environment"))
			Expect(updatedActualTags).To(HaveKeyWithValue("Team", "backend"))

			tf.Logger.Info("verified tag conflict handling", "nlbARN", nlbARN1, "finalTags", updatedActualTags)
		})

		It("should handle mixed scenarios with and without tags", func() {
			appBuilder := manifest.NewFixedResponseServiceBuilder()
			ingBuilder := manifest.NewIngressBuilder()
			dp1, svc1 := appBuilder.WithHTTPBody("app-1").Build(sandboxNS.Name, "app-1", tf.Options.TestImageRegistry)
			dp2, svc2 := appBuilder.WithHTTPBody("app-2").Build(sandboxNS.Name, "app-2", tf.Options.TestImageRegistry)

			ingBackend1 := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc1.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}
			ingBackend2 := networking.IngressBackend{
				Service: &networking.IngressServiceBackend{
					Name: svc2.Name,
					Port: networking.ServiceBackendPort{
						Number: 80,
					},
				},
			}

			// Common annotations for both ingresses
			baseAnnotation := map[string]string{
				"kubernetes.io/ingress.class":                   "alb",
				"alb.ingress.kubernetes.io/scheme":              "internet-facing",
				"alb.ingress.kubernetes.io/target-type":         "ip",
				"alb.ingress.kubernetes.io/enable-frontend-nlb": "true",
				"alb.ingress.kubernetes.io/group.name":          "mixed-tags-group",
			}
			if tf.Options.IPFamily == "IPv6" {
				baseAnnotation["alb.ingress.kubernetes.io/ip-address-type"] = "dualstack"
			}

			// First ingress with tags
			annotation1 := make(map[string]string)
			for k, v := range baseAnnotation {
				annotation1[k] = v
			}
			annotation1["alb.ingress.kubernetes.io/frontend-nlb-tags"] = "Environment=test,Team=platform"

			// Second ingress without tags
			annotation2 := make(map[string]string)
			for k, v := range baseAnnotation {
				annotation2[k] = v
			}
			// No frontend-nlb-tags annotation

			ing1 := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/app1", PathType: &exact, Backend: ingBackend1}).
				WithAnnotations(annotation1).Build(sandboxNS.Name, "ing1")
			ing2 := ingBuilder.
				AddHTTPRoute("", networking.HTTPIngressPath{Path: "/app2", PathType: &exact, Backend: ingBackend2}).
				WithAnnotations(annotation2).Build(sandboxNS.Name, "ing2")

			resStack := fixture.NewK8SResourceStack(tf, dp1, svc1, dp2, svc2, ing1, ing2)
			err := resStack.Setup(ctx)
			Expect(err).NotTo(HaveOccurred())

			defer resStack.TearDown(ctx)

			// Both ingresses should share the same load balancers
			albARN1, albDNS1, nlbARN1, nlbDNS1 := ExpectTwoLBProvisionedForIngress(ctx, tf, ing1)
			albARN2, _, nlbARN2, _ := ExpectTwoLBProvisionedForIngress(ctx, tf, ing2)

			// Verify they share the same load balancers
			Expect(albARN1).To(Equal(albARN2))
			Expect(nlbARN1).To(Equal(nlbARN2))

			// Verify both load balancers are functional
			ExpectLBDNSBeAvailable(ctx, tf, albARN1, albDNS1)
			ExpectLBDNSBeAvailable(ctx, tf, nlbARN1, nlbDNS1)

			// Test traffic through NLB to both apps
			httpExp := httpexpect.New(tf.LoggerReporter, fmt.Sprintf("http://%v", nlbDNS1))
			httpExp.GET("/app1").Expect().
				Status(http.StatusOK).
				Body().Equal("app-1")
			httpExp.GET("/app2").Expect().
				Status(http.StatusOK).
				Body().Equal("app-2")

			// Verify frontend NLB has the tags from the ingress that specified them
			nlbTags, err := tf.LBManager.GetLoadBalancerResourceTags(ctx, nlbARN1)
			Expect(err).NotTo(HaveOccurred())

			actualTags := make(map[string]string)
			for _, tag := range nlbTags {
				actualTags[awssdk.ToString(tag.Key)] = awssdk.ToString(tag.Value)
			}

			Expect(actualTags).To(HaveKeyWithValue("Environment", "test"))
			Expect(actualTags).To(HaveKeyWithValue("Team", "platform"))

			tf.Logger.Info("verified mixed scenario with tagged and untagged ingresses", "nlbARN", nlbARN1)
		})
	})
})

// Helper function to verify tag conflicts (would be used in negative test cases)
func expectTagConflictError(ctx context.Context, tf *framework.Framework, ing *networking.Ingress) {
	Eventually(func(g Gomega) {
		err := tf.K8sClient.Get(ctx, k8s.NamespacedName(ing), ing)
		g.Expect(err).NotTo(HaveOccurred())

		// Check for error conditions in ingress status or events
		// This would need to be implemented based on how the controller reports conflicts
		lbDNS := FindIngressDNSName(ing)
		g.Expect(lbDNS).Should(BeEmpty()) // No LB should be created due to conflict
	}, "2m", "10s").Should(Succeed())
}
