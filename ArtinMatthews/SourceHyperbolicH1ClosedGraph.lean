module

public import ArtinMatthews.SourceHyperbolicH1Integration


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]

def h1InitialGraph (ι : Type*) [Fintype ι] : Submodule ℂ (H1Mass ι × H1Gradient ι) :=
  LinearMap.range ((h1TestMassLinear ι 2).prod (h1TestGradientLinear ι))

def h1TestEquation (φ : h1Tests ι 2) (ij : ι × Fin 3) :
    (H1Mass ι × H1Gradient ι) →L[ℂ] ℂ :=
  (innerSL ℂ (h1TestMass φ)).comp
      ((h1GradientComponent ij).comp (ContinuousLinearMap.snd ℂ (H1Mass ι) (H1Gradient ι))) -
    (innerSL ℂ (h1TestMass (h1AdjointTest φ ij.1 ij.2))).comp
      (ContinuousLinearMap.fst ℂ (H1Mass ι) (H1Gradient ι))

theorem h1InitialGraph_le_test_kernel (φ : h1Tests ι 2) (ij : ι × Fin 3) :
    h1InitialGraph ι ≤ (h1TestEquation φ ij).ker := by
  rintro x ⟨f,rfl⟩
  change inner ℂ (h1TestMass φ) (h1GradientComponent ij (h1TestGradient f)) -
    inner ℂ (h1TestMass (h1AdjointTest φ ij.1 ij.2)) (h1TestMass f) = 0
  exact sub_eq_zero.mpr (h1_first_order_inner φ f ij.1 ij.2)

theorem h1Closure_test_equation {x : H1Mass ι × H1Gradient ι}
    (hx : x ∈ (h1InitialGraph ι).topologicalClosure) (φ : h1Tests ι 2) (ij : ι × Fin 3) :
    inner ℂ (h1TestMass φ) (h1GradientComponent ij x.2) =
      inner ℂ (h1TestMass (h1AdjointTest φ ij.1 ij.2)) x.1 := by
  have h := (h1InitialGraph ι).topologicalClosure_minimal
    (h1InitialGraph_le_test_kernel φ ij) (h1TestEquation φ ij).isClosed_ker hx
  exact sub_eq_zero.mp h

theorem h1GradientComponent_zero {g : H1Gradient ι}
    (hg : ∀ ij : ι × Fin 3, h1GradientComponent ij g = 0) : g=0 := by
  have hpoint (ij : ι × Fin 3) : ∀ᵐ p ∂productVolume ι, g p ij = 0 := by
    filter_upwards [h1GradientComponent_coe ij g,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := productVolume ι)] with p hp hz
    rw [hg ij] at hp
    exact hp.symm.trans hz
  have hall : ∀ᵐ p ∂productVolume ι, ∀ ij : ι × Fin 3, g p ij = 0 :=
    ae_all_iff.mpr hpoint
  apply Lp.ext
  filter_upwards [hall,Lp.coeFn_zero (E := H1Vector ι) (p := 2) (μ := productVolume ι)] with p hp hz
  rw [hz]
  apply (WithLp.equiv 2 (ι × Fin 3 → ℂ)).injective
  funext ij
  exact hp ij

theorem h1InitialGraph_closure_unique (x : H1Mass ι × H1Gradient ι)
    (hx : x ∈ (h1InitialGraph ι).topologicalClosure) (hz : x.1=0) : x.2=0 := by
  apply h1GradientComponent_zero
  intro ij
  have hpair : ∀ φ : h1Tests ι 2, inner ℂ (h1TestMass φ) (h1GradientComponent ij x.2)=0 := by
    intro φ
    rw [h1Closure_test_equation hx φ ij,hz,inner_zero_right]
  apply h1_smooth_test_separates
  intro g hg hc hs
  exact hpair (h1RealTest g (hg.of_le (by simp)) hc hs)

theorem h1Gradient_limit_zero (f : ℕ → h1Tests ι 2) (g : H1Gradient ι)
    (hmass : Tendsto (fun n => h1TestMass (f n)) atTop (𝓝 0))
    (hgrad : Tendsto (fun n => h1TestGradient (f n)) atTop (𝓝 g)) : g=0 := by
  apply h1InitialGraph_closure_unique (0,g) _ rfl
  apply (h1InitialGraph ι).isClosed_topologicalClosure.mem_of_tendsto
    (hmass.prodMk_nhds hgrad)
  exact Filter.Eventually.of_forall fun n =>
    (h1InitialGraph ι).le_topologicalClosure ⟨f n,rfl⟩

theorem h1InitialGraph_unique (x : H1Mass ι × H1Gradient ι)
    (hx : x ∈ h1InitialGraph ι) (hz : x.1=0) : x.2=0 :=
  h1InitialGraph_closure_unique x ((h1InitialGraph ι).le_topologicalClosure hx) hz

def h1InitialGradient (ι : Type*) [Fintype ι] : H1Mass ι →ₗ.[ℂ] H1Gradient ι :=
  (h1InitialGraph ι).toLinearPMap

theorem h1InitialGradient_graph : (h1InitialGradient ι).graph = h1InitialGraph ι :=
  Submodule.toLinearPMap_graph_eq _ h1InitialGraph_unique

theorem h1InitialGradient_isClosable : (h1InitialGradient ι).IsClosable := by
  refine ⟨(h1InitialGradient ι).graph.topologicalClosure.toLinearPMap,?_⟩
  rw [h1InitialGradient_graph]
  exact (Submodule.toLinearPMap_graph_eq _ h1InitialGraph_closure_unique).symm

def h1WeakGradient (ι : Type*) [Fintype ι] : H1Mass ι →ₗ.[ℂ] H1Gradient ι :=
  (h1InitialGradient ι).closure

theorem h1WeakGradient_closed : (h1WeakGradient ι).IsClosed :=
  h1InitialGradient_isClosable.closure_isClosed

theorem h1InitialGradient_dense_domain : Dense ((h1InitialGradient ι).domain : Set (H1Mass ι)) := by
  apply (h1TestMass_denseRange (ι := ι) 2 (by simp)).mono
  rintro x ⟨f,rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph
  rw [h1InitialGradient_graph]
  exact ⟨f,rfl⟩

theorem h1WeakGradient_dense_domain : Dense ((h1WeakGradient ι).domain : Set (H1Mass ι)) :=
  h1InitialGradient_dense_domain.mono (LinearPMap.le_closure (h1InitialGradient ι)).1

end
end ArtinMatthews.SourceHyperbolicGreen
