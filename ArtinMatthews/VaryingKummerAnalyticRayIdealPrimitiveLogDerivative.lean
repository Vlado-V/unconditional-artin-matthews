module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealLogDerivative
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual primitive entire continuation inherits the universal
right-half-plane logarithmic-derivative estimate from its genuine ideal
Euler product. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Set Filter
open scoped NumberField Topology
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hnp : ψ.IsNonprincipal)
include hnp

theorem primitiveContinued_logDeriv_eq_dirichlet {s : ℂ} (hs : 1 < s.re) :
    logDeriv (ψ.primitiveContinued hM hprim) s = logDeriv ψ.dirichlet s := by
  have heq : ψ.primitiveContinued hM hprim =ᶠ[𝓝 s] ψ.dirichlet := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact ψ.primitiveContinued_eq_dirichlet hM hprim hnp hz
  rw [logDeriv_apply,logDeriv_apply,heq.deriv_eq,heq.eq_of_nhds]

theorem primitiveContinued_logDeriv_norm_le {s : ℂ} (hs : (3/2:ℝ) ≤ s.re) :
    ‖logDeriv (ψ.primitiveContinued hM hprim) s‖ ≤
      dedekindLogDerivUniformConstant * (Module.finrank ℚ K:ℝ) := by
  rw [ψ.primitiveContinued_logDeriv_eq_dirichlet hM hprim hnp (by linarith)]
  exact ψ.dirichlet_logDeriv_norm_le hs

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
