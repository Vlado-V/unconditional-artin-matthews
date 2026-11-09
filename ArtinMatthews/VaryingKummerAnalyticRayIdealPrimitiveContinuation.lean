module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealConductorOne
public import ArtinMatthews.VaryingKummerAnalyticRayIdealRamifiedContinuation
public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine entire continuation of each nonprincipal primitive ideal-ray
series, including the unramified unit-conductor class-character case. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

def primitiveContinued (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) : ℂ → ℂ :=
  if hres : ψ.residue = 1 then
    ψ.conductorOneContinued (idealConductor_top_of_primitive_residue_one ψ.residue hprim hres)
  else ψ.ramifiedContinued hM

theorem primitiveContinued_entire (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    Differentiable ℂ (ψ.primitiveContinued hM hprim) := by
  unfold primitiveContinued
  split_ifs with hres
  · exact ψ.conductorOneContinued_entire _
  · exact ψ.ramifiedContinued_entire hM hres

theorem primitiveContinued_eq_dirichlet (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {s : ℂ} (hs : 1 < s.re) :
    ψ.primitiveContinued hM hprim s = ψ.dirichlet s := by
  unfold primitiveContinued
  split_ifs with hres
  · exact ψ.conductorOneContinued_eq_dirichlet _ hnp hs
  · exact ψ.ramifiedContinued_eq_dirichlet hM hres hs

theorem primitiveContinued_ne_zero_right (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {s : ℂ} (hs : 1 < s.re) :
    ψ.primitiveContinued hM hprim s ≠ 0 := by
  rw [ψ.primitiveContinued_eq_dirichlet hM hprim hnp hs]
  exact ψ.dirichlet_ne_zero hs

theorem primitiveContinued_ne_zero (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) : ψ.primitiveContinued hM hprim ≠ 0 := by
  intro hzero
  exact ψ.primitiveContinued_ne_zero_right hM hprim hnp (s := 2) (by norm_num)
    (congrFun hzero 2)

theorem primitiveContinued_finite_nonnegative_order (hM : M ≠ ⊥)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) (β : ℂ) :
    ∃ m : ℕ, meromorphicOrderAt (ψ.primitiveContinued hM hprim) β = (m : WithTop ℤ) := by
  have ha : ∀ z, AnalyticAt ℂ (ψ.primitiveContinued hM hprim) z :=
    fun z => (ψ.primitiveContinued_entire hM hprim).analyticAt z
  have hfin : analyticOrderAt (ψ.primitiveContinued hM hprim) β ≠ ⊤ := by
    intro hz
    exact ψ.primitiveContinued_ne_zero hM hprim hnp
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero β ha).mp hz)
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m,?_⟩
  rw [(ha β).meromorphicOrderAt_eq,← hm,ENat.map_natCast]
  rfl

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
