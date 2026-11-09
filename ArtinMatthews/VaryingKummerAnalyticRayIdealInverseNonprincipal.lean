module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverse
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! Actual nonprincipality and primitivity pass to the inverse ideal character. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M)

theorem inverse_isNonprincipal (hψ : ψ.IsNonprincipal) : ψ.inverse.IsNonprincipal := by
  obtain ⟨I,hI,hcop,hval⟩ := hψ
  refine ⟨I,hI,hcop,?_⟩
  rw [inverse_idealHom]
  exact inv_ne_one.mpr hval

theorem inverse_isPrimitive (hM : M ≠ ⊥)
    (hψ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.inverse.residue := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
  exact hψ.inv

theorem inverse_residue_ne_one (hψ : ψ.residue ≠ 1) : ψ.inverse.residue ≠ 1 := by
  rw [inverse_residue]
  exact inv_ne_one.mpr hψ

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
