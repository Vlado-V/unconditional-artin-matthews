module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealConjugation


set_option backward.privateInPublic true
@[expose] public section

/-! Self-duality of the actual ideal series and primitive continuation
for a real-valued finite-order ideal character. -/
namespace ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
open NumberField FractionalIdeal Set
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)
variable (hreal : ∀ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
  star (ψ.idealHom J : ℂ) = (ψ.idealHom J : ℂ))
include hreal

theorem inverse_coefficient_eq_of_real (J : integralFractionalIdeals K) :
    ψ.inverse.coefficient J = ψ.coefficient J := by
  rw [ψ.inverse_coefficient_conj]
  unfold coefficient
  split_ifs
  · exact hreal J.val
  · exact map_zero _

theorem inverse_dirichlet_eq_of_real (s : ℂ) :
    ψ.inverse.dirichlet s = ψ.dirichlet s := by
  unfold dirichlet
  apply tsum_congr
  intro J
  rw [ψ.inverse_coefficient_eq_of_real hreal]

theorem primitiveContinued_inverse_eq_of_real (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) (s : ℂ) :
    ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) s =
      ψ.primitiveContinued hM hprim s := by
  let f := ψ.primitiveContinued hM hprim
  let g := ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim)
  have hf : Differentiable ℂ f := ψ.primitiveContinued_entire hM hprim
  have hg : Differentiable ℂ g := ψ.inverse.primitiveContinued_entire hM _
  have he : g = f := by
    apply (hg.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      (hf.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2 : ℂ))
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)] with z hz
    dsimp only [f, g]
    rw [ψ.inverse.primitiveContinued_eq_dirichlet hM _
      (ψ.inverse_isNonprincipal hnp) hz,
      ψ.primitiveContinued_eq_dirichlet hM hprim hnp hz]
    exact ψ.inverse_dirichlet_eq_of_real hreal z
  exact congrFun he s

end
end ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
