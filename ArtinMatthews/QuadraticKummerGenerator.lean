module

public import ArtinMatthews.QuadraticKummer
public import Mathlib.FieldTheory.Galois.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The concrete square root generates the whole singleton radical field. -/
namespace ArtinMatthews
open scoped Classical
noncomputable section
variable {F : Type} [Field F] [CharZero F] [Algebra F ℂ]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 6)

include hζ

theorem quadraticKummerRoot_adjoin (u : Fˣ) :
    IntermediateField.adjoin F {quadraticKummerRoot u} = ⊤ := by
  let A := IntermediateField.adjoin F {quadraticKummerRoot u}
  have hfix : A.fixingSubgroup = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro σ hσ
    change σ = 1
    apply quadraticKummerCharacter_injective hζ u
    rw [map_one]
    apply Units.ext
    rw [quadraticKummerCharacter_eq_rootRatio]
    have hβ : σ (quadraticKummerRoot u) = quadraticKummerRoot u :=
      (IntermediateField.mem_fixingSubgroup_iff A σ).mp hσ _
        (IntermediateField.subset_adjoin F _ (Set.mem_singleton _))
    rw [hβ, div_self (quadraticKummerRoot_ne_zero u)]
    rfl
  have h := IsGalois.fixedField_fixingSubgroup A
  rw [hfix, IntermediateField.fixedField_bot] at h
  exact h.symm

end
end ArtinMatthews
