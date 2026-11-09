module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverseNonprincipal
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.LogDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! Conjugation of the actual primitive ideal-character continuation, proved
from its genuine ideal series and analytic uniqueness. No functional equation
is used. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Set
open scoped NumberField nonZeroDivisors Classical ComplexConjugate
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

theorem inverse_dirichlet_conj (s : ℂ) :
    ψ.inverse.dirichlet (conj s) = conj (ψ.dirichlet s) := by
  unfold dirichlet
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro J
  rw [inverse_coefficient_conj, map_mul]
  congr 1
  have hp : (((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (fractionalIdeal_absNorm_pos J.val).le]
    exact ne_of_lt Real.pi_pos
  simpa only [map_neg, Complex.conj_ofReal] using
    Complex.cpow_conj (((FractionalIdeal.absNorm J.val.val : ℝ) : ℂ)) (-s) hp

variable (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hnp

/-- Exact conjugation pairs the actual continuations of inverse characters. -/
theorem primitiveContinued_inverse_conj (s : ℂ) :
    ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) (conj s) =
      conj (ψ.primitiveContinued hM hprim s) := by
  let f := ψ.primitiveContinued hM hprim
  let g := ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)
  have hf : Differentiable ℂ f := ψ.primitiveContinued_entire hM hprim
  have hg : Differentiable ℂ g := ψ.inverse.primitiveContinued_entire hM _
  have hc : Differentiable ℂ (fun z => conj (f (conj z))) := by
    intro z
    simpa only [Function.comp_def, starRingEnd_self_apply] using (hf (conj z)).conj_conj
  have he : g = fun z => conj (f (conj z)) := by
    apply (hg.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      (hc.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2:ℂ))
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    dsimp only [f,g]
    rw [ψ.inverse.primitiveContinued_eq_dirichlet hM _ (ψ.inverse_isNonprincipal hnp) hz,
      ψ.primitiveContinued_eq_dirichlet hM hprim hnp (by simpa using hz)]
    simpa only [starRingEnd_self_apply] using ψ.inverse_dirichlet_conj (conj z)
  simpa only [starRingEnd_self_apply] using congrFun he (conj s)

theorem primitiveContinued_inverse_zero_iff (s : ℂ) :
    ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) (conj s) = 0 ↔
      ψ.primitiveContinued hM hprim s = 0 := by
  rw [ψ.primitiveContinued_inverse_conj hM hprim hnp]
  exact map_eq_zero_iff _ (starRingEnd ℂ).injective

theorem primitiveContinued_inverse_logDeriv_conj (s : ℂ) :
    logDeriv (ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)) (conj s) =
      conj (logDeriv (ψ.primitiveContinued hM hprim) s) := by
  have he : conj ∘ ψ.primitiveContinued hM hprim ∘ conj =
      ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) := by
    funext z
    simpa only [Function.comp_apply,starRingEnd_self_apply] using
      (ψ.primitiveContinued_inverse_conj hM hprim hnp (conj z)).symm
  have hd := congrFun (deriv_conj_conj (f := ψ.primitiveContinued hM hprim)) (conj s)
  rw [he] at hd
  simp only [Function.comp_apply,starRingEnd_self_apply] at hd
  rw [logDeriv_apply,logDeriv_apply,hd,
    ψ.primitiveContinued_inverse_conj hM hprim hnp,map_div₀]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
