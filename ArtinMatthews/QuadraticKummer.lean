module

public import ArtinMatthews.KummerRowField
public import ArtinMatthews.KummerRowDegree
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex


set_option backward.privateInPublic true
@[expose] public section

/-! The actual quadratic radical field as the singleton sixth-radical
field of the cubed parameter. Its radical character is faithful and
takes values in the square roots of unity. -/
namespace ArtinMatthews
open scoped Classical
noncomputable section
variable {F : Type} [Field F] [Algebra F ℂ]

abbrev QuadraticKummerField (u : Fˣ) := sixthKummerRowField ({(u : F) ^ 3} : Finset F)

def quadraticKummerSixthRoot (u : Fˣ) : QuadraticKummerField u :=
  sixthKummerRowRoot {(u : F) ^ 3} ((u : F) ^ 3) (Finset.mem_singleton_self _)

theorem quadraticKummerSixthRoot_pow (u : Fˣ) :
    quadraticKummerSixthRoot u ^ 6 = (algebraMap F (QuadraticKummerField u) (u : F)) ^ 3 := by
  rw [quadraticKummerSixthRoot, sixthKummerRowRoot_pow, map_pow]

theorem quadraticKummerSixthRoot_ne_zero (u : Fˣ) : quadraticKummerSixthRoot u ≠ 0 :=
  sixthKummerRowRoot_ne_zero _ _ _ (pow_ne_zero _ u.ne_zero)

def quadraticKummerRoot (u : Fˣ) : QuadraticKummerField u :=
  quadraticKummerSixthRoot u ^ 3 / algebraMap F (QuadraticKummerField u) (u : F)

theorem quadraticKummerRoot_sq (u : Fˣ) :
    quadraticKummerRoot u ^ 2 = algebraMap F (QuadraticKummerField u) (u : F) := by
  have hu := (map_ne_zero (algebraMap F (QuadraticKummerField u))).mpr u.ne_zero
  rw [quadraticKummerRoot, div_pow, ← pow_mul, show (3 : ℕ) * 2 = 6 by decide,
    quadraticKummerSixthRoot_pow]
  exact (div_eq_iff (pow_ne_zero _ hu)).2 (by ring)

theorem quadraticKummerRoot_ne_zero (u : Fˣ) : quadraticKummerRoot u ≠ 0 :=
  div_ne_zero (pow_ne_zero _ (quadraticKummerSixthRoot_ne_zero u))
    ((map_ne_zero (algebraMap F (QuadraticKummerField u))).mpr u.ne_zero)

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 6)

def quadraticKummerCharacter (u : Fˣ) : Gal(QuadraticKummerField u/F) →* ℂˣ :=
  sixthKummerRowCharacter hζ {(u : F) ^ 3} ((u : F) ^ 3) (Finset.mem_singleton_self _)
    (pow_ne_zero _ u.ne_zero)

theorem quadraticKummerCharacter_apply (u : Fˣ) (σ : Gal(QuadraticKummerField u/F)) :
    (quadraticKummerCharacter hζ u σ : ℂ) =
      ((σ (quadraticKummerSixthRoot u) / quadraticKummerSixthRoot u : QuadraticKummerField u) : ℂ) :=
  rfl

theorem quadraticKummerCharacter_injective (u : Fˣ) :
    Function.Injective (quadraticKummerCharacter hζ u) := by
  let A : Finset F := {(u : F) ^ 3}
  have hA : ∀ a ∈ A, a ≠ 0 := by
    intro a ha
    rw [Finset.mem_singleton.mp ha]
    exact pow_ne_zero _ u.ne_zero
  intro σ τ h
  apply sixthKummerRowRootsMap_injective hζ A hA
  funext a
  obtain ⟨a, ha⟩ := a
  obtain rfl := Finset.mem_singleton.mp ha
  apply sixthKummerRootUnityComplex_injective A
  exact h

include hζ in
theorem quadraticKummerSixthRoot_ratio_sq (u : Fˣ) (σ : Gal(QuadraticKummerField u/F)) :
    (σ (quadraticKummerSixthRoot u) / quadraticKummerSixthRoot u) ^ 2 = 1 := by
  let a := algebraMap F (QuadraticKummerField u) (u : F)
  let x := quadraticKummerSixthRoot u
  have ha : a ≠ 0 := (map_ne_zero (algebraMap F (QuadraticKummerField u))).mpr u.ne_zero
  have hx : x ≠ 0 := quadraticKummerSixthRoot_ne_zero u
  have hp : x ^ 6 = a ^ 3 := quadraticKummerSixthRoot_pow u
  have hz : (x ^ 2 / a) ^ 6 = 1 := by
    rw [div_pow, ← pow_mul, show (2 : ℕ) * 6 = 6 * 2 by decide, pow_mul, hp,
      ← pow_mul, show (3 : ℕ) * 2 = 6 by decide, div_self (pow_ne_zero _ ha)]
  have hh := radical_aut_fixes_rootsOfUnity hζ σ hz
  rw [map_div₀, map_pow, show σ a = a from σ.commutes _] at hh
  have hsq := (div_left_inj' ha).mp hh
  change (σ x / x) ^ 2 = 1
  rw [div_pow, hsq, div_self (pow_ne_zero _ hx)]

theorem quadraticKummerCharacter_sq (u : Fˣ) (σ : Gal(QuadraticKummerField u/F)) :
    quadraticKummerCharacter hζ u σ ^ 2 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, quadraticKummerCharacter_apply, ← IntermediateField.coe_pow,
    quadraticKummerSixthRoot_ratio_sq hζ u σ]
  rfl

theorem quadraticKummerCharacter_eq_rootRatio (u : Fˣ) (σ : Gal(QuadraticKummerField u/F)) :
    (quadraticKummerCharacter hζ u σ : ℂ) =
      ((σ (quadraticKummerRoot u) / quadraticKummerRoot u : QuadraticKummerField u) : ℂ) := by
  rw [quadraticKummerCharacter_apply]
  apply congrArg (fun z : QuadraticKummerField u => (z : ℂ))
  let a := algebraMap F (QuadraticKummerField u) (u : F)
  let x := quadraticKummerSixthRoot u
  have ha : a ≠ 0 := (map_ne_zero (algebraMap F (QuadraticKummerField u))).mpr u.ne_zero
  have hx : x ≠ 0 := quadraticKummerSixthRoot_ne_zero u
  have hsq : (σ x / x) ^ 2 = 1 := quadraticKummerSixthRoot_ratio_sq hζ u σ
  change σ x / x = σ (x ^ 3 / a) / (x ^ 3 / a)
  rw [map_div₀, map_pow, show σ a = a from σ.commutes _, div_div_div_cancel_right₀ ha, ← div_pow]
  rw [show (3 : ℕ) = 2 + 1 by decide, pow_add, hsq, one_mul, pow_one]

omit [Algebra F ℂ] in
theorem quadraticKummer_sixthCube_iff_square (u : Fˣ) :
    (∃ x : F, x ^ 6 = (u : F) ^ 3) ↔ ∃ y : F, y ^ 2 = (u : F) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x ^ 3 / (u : F), ?_⟩
    rw [div_pow, ← pow_mul, show (3 : ℕ) * 2 = 6 by decide, hx,
      div_eq_iff (pow_ne_zero _ u.ne_zero)]
    ring
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [← hy, ← pow_mul]⟩

theorem quadraticKummerCharacter_one_iff [CharZero F] (u : Fˣ) :
    quadraticKummerCharacter hζ u = 1 ↔ ∃ y : F, y ^ 2 = (u : F) :=
  (sixthKummerRowCharacter_one_iff_exists_sixthPower hζ _ _ _
    (pow_ne_zero _ u.ne_zero)).trans (quadraticKummer_sixthCube_iff_square u)

include hζ in
theorem quadraticKummerField_finrank_dvd_two [CharZero F] (u : Fˣ) :
    Module.finrank F (QuadraticKummerField u) ∣ 2 := by
  let φ : Gal(QuadraticKummerField u/F) →* rootsOfUnity 2 ℂ :=
    (quadraticKummerCharacter hζ u).codRestrict (rootsOfUnity 2 ℂ)
      (fun σ => (mem_rootsOfUnity _ _).2 (quadraticKummerCharacter_sq hζ u σ))
  have hinj : Function.Injective φ := fun _ _ h =>
    quadraticKummerCharacter_injective hζ u (congrArg Subtype.val h)
  have h := Subgroup.card_dvd_of_injective φ hinj
  rwa [IsGalois.card_aut_eq_finrank, Complex.card_rootsOfUnity] at h

end
end ArtinMatthews
