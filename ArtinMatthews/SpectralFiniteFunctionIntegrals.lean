module

public import ArtinMatthews.SpectralGamma0FourierGeometric


set_option backward.privateInPublic true
@[expose] public section

/-! Integral exchange for families having genuinely finite support as
functions.  This is stronger than pointwise finite support. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem finiteFunctionSupport_eval {ι X : Type*} (F : ι → X → ℂ)
    (hF : Function.HasFiniteSupport F) (x : X) :
    Function.HasFiniteSupport (fun i => F i x) := by
  apply hF.subset
  intro i hi hzero
  exact hi (congrFun hzero x)

theorem finiteFunctionSupport_finsum_eq_sum {ι X : Type*} (F : ι → X → ℂ)
    (hF : Function.HasFiniteSupport F) (x : X) :
    (∑ᶠ i, F i x) = ∑ i ∈ hF.toFinset, F i x := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply hF.mem_toFinset.mpr
  intro hzero
  exact hi (congrFun hzero x)

theorem finiteFunctionSupport_integrable {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ι → X → ℂ) (hF : Function.HasFiniteSupport F)
    (hI : ∀ i, Integrable (F i) μ) : Integrable (fun x => ∑ᶠ i, F i x) μ := by
  classical
  have he : (fun x => ∑ᶠ i, F i x) = fun x => ∑ i ∈ hF.toFinset, F i x :=
    funext (finiteFunctionSupport_finsum_eq_sum F hF)
  rw [he]
  exact integrable_finsetSum _ (fun i _ => hI i)

theorem finiteFunctionSupport_integral {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ι → X → ℂ) (hF : Function.HasFiniteSupport F)
    (hI : ∀ i, Integrable (F i) μ) :
    (∫ x, (∑ᶠ i, F i x) ∂μ) = ∑ᶠ i, ∫ x, F i x ∂μ := by
  classical
  have hs : Function.support (fun i => ∫ x, F i x ∂μ) ⊆ hF.toFinset := by
    intro i hi
    apply hF.mem_toFinset.mpr
    intro hzero
    apply hi
    change (∫ x, F i x ∂μ) = 0
    simp only [hzero,Pi.zero_apply,integral_zero]
  simp_rw [finiteFunctionSupport_finsum_eq_sum F hF]
  rw [integral_finsetSum _ (fun i _ => hI i), finsum_eq_sum_of_support_subset _ hs]

theorem finiteFunctionSupport_fibre {ι κ X : Type*} (F : ι × κ → X → ℂ)
    (hF : Function.HasFiniteSupport F) (i : ι) :
    Function.HasFiniteSupport (fun j => F (i,j)) :=
  Function.HasFiniteSupport.fun_comp_of_injective (f := F)
    (g := fun j => (i,j)) (fun _ _ h => congrArg Prod.snd h) hF

theorem finiteFunctionSupport_fibre_sum {ι κ X : Type*} (F : ι × κ → X → ℂ)
    (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (fun i x => ∑ᶠ j, F (i,j) x) := by
  apply (hF.image Prod.fst).subset
  intro i hi
  by_contra hnot
  apply hi
  funext x
  have hz (j : κ) : F (i,j) = 0 := by
    by_contra hj
    exact hnot ⟨(i,j),hj,rfl⟩
  simp only [hz,Pi.zero_apply,finsum_zero]

end ArtinMatthews
