module

public import ArtinMatthews.KummerRowDegree


set_option backward.privateInPublic true
@[expose] public section

/-! The individual sixth-radical field has degree dividing six. This
divisibility belongs to the one-parameter field, not to a common row
compositum. -/
namespace ArtinMatthews
open scoped Classical
noncomputable section

variable {F : Type*} [Field F] [Algebra F ℂ] [CharZero F]

theorem sixthKummerIndividualField_finrank_dvd_six {ζ : F}
    (hζ : IsPrimitiveRoot ζ 6) (a : F) (ha : a ≠ 0) :
    Module.finrank F (sixthKummerRowField {a}) ∣ 6 := by
  have hA : ∀ b ∈ ({a} : Finset F), b ≠ 0 := by simpa using ha
  have hc := Subgroup.card_dvd_of_injective (sixthKummerRowRootsMap hζ {a} hA)
    (sixthKummerRowRootsMap_injective hζ {a} hA)
  rw [IsGalois.card_aut_eq_finrank,Nat.card_fun,
    (hζ.map_of_injective (algebraMap F (sixthKummerRowField {a})).injective).card_rootsOfUnity,
    Nat.card_eq_finsetCard,Finset.card_singleton,pow_one] at hc
  exact hc

theorem sixthKummerIndividualField_exists_divisor_degree {ζ : F}
    (hζ : IsPrimitiveRoot ζ 6) (a : F) (ha : a ≠ 0) :
    Module.finrank F (sixthKummerRowField {a})=1 ∨
      Module.finrank F (sixthKummerRowField {a})=2 ∨
      Module.finrank F (sixthKummerRowField {a})=3 ∨
      Module.finrank F (sixthKummerRowField {a})=6 := by
  have h := sixthKummerIndividualField_finrank_dvd_six hζ a ha
  have hp : 0 < Module.finrank F (sixthKummerRowField {a}) := Module.finrank_pos
  have hd := Nat.le_of_dvd (by decide : 0 < 6) h
  interval_cases hdeg : Module.finrank F (sixthKummerRowField {a}) <;> norm_num at *

end
end ArtinMatthews
