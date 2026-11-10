module

public import ArtinMatthews.KummerRowField
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Literal uniform degree control of the finite sixth-radical row field.
The actual automorphism group embeds in one copy of the sixth roots of
unity per nonzero parameter. No irreducibility or independence is assumed. -/
namespace ArtinMatthews
open scoped Classical
noncomputable section
variable {F : Type*} [Field F] [Algebra F ℂ] {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
variable (A : Finset F) (hA : ∀ a ∈ A, a ≠ 0)

def sixthKummerRowRootsMap :
    Gal(sixthKummerRowField A/F) →* ({a // a ∈ A} → rootsOfUnity 6 (sixthKummerRowField A)) :=
  MonoidHom.pi fun a => radicalAutCharacter hζ (sixthKummerRowRoot_pow A a.val a.property)
    (sixthKummerRowRoot_ne_zero A a.val a.property (hA a.val a.property))

theorem sixthKummerRowRootsMap_injective : Function.Injective (sixthKummerRowRootsMap hζ A hA) := by
  intro σ τ h
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.adjoin_algHom_ext F
  intro z hz
  let x : sixthKummerRowField A := ⟨z,IntermediateField.subset_adjoin F _ hz⟩
  change σ x = τ x
  rcases (mem_sixthKummerRowPolynomial_rootSet A z).mp hz with hx | ⟨a,ha,hx⟩
  · have hx' : x^6 = 1 := by
      apply Subtype.ext
      simpa only [IntermediateField.coe_pow,IntermediateField.coe_one] using hx
    rw [radical_aut_fixes_rootsOfUnity hζ σ hx',radical_aut_fixes_rootsOfUnity hζ τ hx']
  · let y := sixthKummerRowRoot A a ha
    have hy0 : y ≠ 0 := sixthKummerRowRoot_ne_zero A a ha (hA a ha)
    have hy : y^6 = algebraMap F (sixthKummerRowField A) a := sixthKummerRowRoot_pow A a ha
    have hx' : x^6 = algebraMap F (sixthKummerRowField A) a := Subtype.ext hx
    have hrow := congrFun h (⟨a,ha⟩ : {a // a ∈ A})
    have hratio := congrArg (fun w : rootsOfUnity 6 (sixthKummerRowField A) =>
      ((w : (sixthKummerRowField A)ˣ) : sixthKummerRowField A)) hrow
    change σ y / y = τ y / y at hratio
    have hroot : σ y = τ y := (div_left_inj' hy0).mp hratio
    let r := x/y
    have hr : r^6 = 1 := by
      dsimp [r]
      rw [div_pow,hx',hy,div_self]
      rw [← hy]
      exact pow_ne_zero _ hy0
    have hσr := radical_aut_fixes_rootsOfUnity hζ σ hr
    have hτr := radical_aut_fixes_rootsOfUnity hζ τ hr
    have hsplit : x = r*y := (div_mul_cancel₀ x hy0).symm
    rw [hsplit,map_mul,map_mul,hσr,hτr,hroot]

include hζ hA in
theorem sixthKummerRowField_finrank_le [CharZero F] :
    Module.finrank F (sixthKummerRowField A) ≤ 6^A.card := by
  have H := Nat.card_le_card_of_injective (sixthKummerRowRootsMap hζ A hA)
    (sixthKummerRowRootsMap_injective hζ A hA)
  rw [IsGalois.card_aut_eq_finrank,Nat.card_fun,
    (hζ.map_of_injective (algebraMap F (sixthKummerRowField A)).injective).card_rootsOfUnity,
    Nat.card_eq_finsetCard] at H
  exact H

end
end ArtinMatthews
