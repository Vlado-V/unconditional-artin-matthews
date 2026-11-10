module

public import ArtinMatthews.CubicTrace
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc


set_option backward.privateInPublic true
@[expose] public section

/-!
# Finite Fourier inversion for the cubic Frobenius condition

We write the finite abelian group additively. Thus negation represents group
inversion, and the zero additive character is the trivial multiplicative
character. All expansions below are proved from character orthogonality.
-/

noncomputable section
open scoped BigOperators

namespace ArtinMatthews

variable {H : Type*} [AddCommGroup H] [Fintype H]

/-- The Fourier coefficient of the indicator of a finite set. -/
def indicatorFourierCoeff (C : Finset H) (χ : AddChar H ℂ) : ℂ :=
  (∑ g ∈ C, χ (-g)) / Fintype.card H

/-- Finite Fourier inversion, derived from the orthogonality of all characters. -/
theorem indicator_fourier_expansion [DecidableEq H] (C : Finset H) (h : H) :
    (if h ∈ C then (1 : ℂ) else 0) =
      ∑ χ : AddChar H ℂ, indicatorFourierCoeff C χ * χ h := by
  classical
  have hcard : (Fintype.card H : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  symm
  calc
    _ = (∑ χ : AddChar H ℂ, ∑ g ∈ C, χ (h - g)) / Fintype.card H := by
      simp_rw [indicatorFourierCoeff, div_mul_eq_mul_div, Finset.sum_div,
        Finset.sum_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
      simp only [mul_comm, Finset.sum_div]
    _ = (∑ g ∈ C, ∑ χ : AddChar H ℂ, χ (h - g)) / Fintype.card H := by
      rw [Finset.sum_comm]
    _ = (∑ g ∈ C, if h = g then (Fintype.card H : ℂ) else 0) /
        Fintype.card H := by simp_rw [AddChar.sum_apply_eq_ite, sub_eq_zero]
    _ = if h ∈ C then 1 else 0 := by
      by_cases hh : h ∈ C <;> simp [hh, hcard]

@[simp] theorem indicatorFourierCoeff_zero (C : Finset H) :
    indicatorFourierCoeff C 0 = (C.card : ℂ) / Fintype.card H := by
  simp [indicatorFourierCoeff]

/-- In additive notation, inversion stability means stability under negation. -/
def InversionStable (C : Finset H) : Prop := ∀ g, g ∈ C ↔ -g ∈ C

/-- For an inversion-stable set the sign in the coefficient can be omitted. -/
theorem indicatorFourierCoeff_eq_positive (C : Finset H) (hC : InversionStable C)
    (χ : AddChar H ℂ) :
    indicatorFourierCoeff C χ = (∑ g ∈ C, χ g) / Fintype.card H := by
  unfold indicatorFourierCoeff
  congr 1
  exact Finset.sum_bij (fun g _ => -g)
    (fun g hg => (hC g).mp hg)
    (fun _ _ _ _ h => neg_injective h)
    (fun g hg => ⟨-g, (hC g).mp hg, neg_neg g⟩)
    (fun _ _ => rfl)

/-- Opposite characters have equal coefficients for inversion-stable sets. -/
theorem indicatorFourierCoeff_neg (C : Finset H) (hC : InversionStable C)
    (χ : AddChar H ℂ) :
    indicatorFourierCoeff C (-χ) = indicatorFourierCoeff C χ := by
  rw [indicatorFourierCoeff_eq_positive C hC]
  rfl

/-- The coefficients of an inversion-stable indicator are real. -/
theorem indicatorFourierCoeff_conj (C : Finset H) (hC : InversionStable C)
    (χ : AddChar H ℂ) :
    star (indicatorFourierCoeff C χ) = indicatorFourierCoeff C χ := by
  rw [indicatorFourierCoeff_eq_positive C hC]
  simp only [star_div₀, star_sum, star_natCast, Complex.star_def, ← AddChar.map_neg_eq_conj]
  exact indicatorFourierCoeff_eq_positive C hC χ

/-- An explicit real-value form of the preceding coefficient identity. -/
theorem indicatorFourierCoeff_re (C : Finset H) (hC : InversionStable C)
    (χ : AddChar H ℂ) :
    ((indicatorFourierCoeff C χ).re : ℂ) = indicatorFourierCoeff C χ :=
  Complex.conj_eq_iff_re.mp (indicatorFourierCoeff_conj C hC χ)

omit [Fintype H] in
/-- Characters of a group annihilated by three take values in the cube roots of unity. -/
theorem character_cube_eq_one (hH : ∀ h : H, (3 : ℕ) • h = 0)
    (χ : AddChar H ℂ) (h : H) : (χ h) ^ 3 = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, hH h, AddChar.map_zero_eq_one]

omit [Fintype H] in
/-- Negation has no fixed nontrivial character in exponent three. -/
theorem character_neg_eq_self_iff (hH : ∀ h : H, (3 : ℕ) • h = 0)
    (χ : AddChar H ℂ) : -χ = χ ↔ χ = 0 := by
  constructor
  · intro heq
    have hthree : (3 : ℕ) • χ = 0 := by
      ext h
      simpa only [AddChar.nsmul_apply, AddChar.zero_apply] using character_cube_eq_one hH χ h
    have htwo : χ + χ = 0 := by nth_rw 1 [← heq]; exact neg_add_cancel χ
    have hsum : (3 : ℕ) • χ = χ := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, two_nsmul, htwo, zero_add]
    exact hsum.symm.trans hthree
  · rintro rfl
    exact neg_zero

/-- One representative from each pair of nontrivial opposite characters, chosen
using an arbitrary enumeration of the finite character group. -/
def characterPairReps : Finset (AddChar H ℂ) :=
  Finset.univ.filter fun χ =>
    Fintype.equivFin (AddChar H ℂ) χ < Fintype.equivFin (AddChar H ℂ) (-χ)

/-- The representative set and its negative are disjoint and exhaust exactly
the nontrivial characters. -/
theorem characterPairReps_spec (hH : ∀ h : H, (3 : ℕ) • h = 0) :
    (0 : AddChar H ℂ) ∉ characterPairReps (H := H) ∧
    Disjoint (characterPairReps (H := H)) ((characterPairReps (H := H)).image Neg.neg) ∧
    characterPairReps (H := H) ∪ (characterPairReps (H := H)).image Neg.neg =
      Finset.univ.erase 0 := by
  classical
  let e := Fintype.equivFin (AddChar H ℂ)
  have hmem (χ : AddChar H ℂ) : χ ∈ characterPairReps (H := H) ↔ e χ < e (-χ) := by
    simp [characterPairReps, e]
  have hzero : (0 : AddChar H ℂ) ∉ characterPairReps (H := H) := by
    simp [hmem]
  refine ⟨hzero, Finset.disjoint_left.mpr ?_, ?_⟩
  · intro χ hχ himage
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp himage
    have h₁ := (hmem ψ).mp hψ
    have h₂ := (hmem (-ψ)).mp hχ
    exact (lt_asymm h₁) (by simpa using h₂)
  · ext χ
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (hχ | ⟨ψ, hψ, rfl⟩)
      · intro heq
        exact hzero (heq ▸ hχ)
      · intro heq
        exact hzero ((neg_eq_zero.mp heq) ▸ hψ)
    · intro hχ
      have hne : e χ ≠ e (-χ) := by
        intro heq
        exact hχ ((character_neg_eq_self_iff hH χ).mp (e.injective heq).symm)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ((hmem χ).mpr hlt)
      · exact Or.inr ⟨-χ, (hmem (-χ)).mpr (by simpa using hgt), neg_neg χ⟩

/-- Pairing all nontrivial characters with their inverses. -/
theorem sum_character_pairs (hH : ∀ h : H, (3 : ℕ) • h = 0)
    (f : AddChar H ℂ → ℂ) :
    (∑ χ : AddChar H ℂ, f χ) = f 0 +
      ∑ χ ∈ characterPairReps (H := H), (f χ + f (-χ)) := by
  classical
  obtain ⟨_, hdisj, hunion⟩ := characterPairReps_spec hH
  calc
    _ = f 0 + ∑ χ ∈ (Finset.univ.erase 0), f χ := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ _)]
    _ = f 0 + ∑ χ ∈ characterPairReps (H := H) ∪
        (characterPairReps (H := H)).image Neg.neg, f χ := by rw [hunion]
    _ = f 0 + ((∑ χ ∈ characterPairReps (H := H), f χ) +
        ∑ χ ∈ (characterPairReps (H := H)).image Neg.neg, f χ) := by
      rw [Finset.sum_union hdisj]
    _ = f 0 + ((∑ χ ∈ characterPairReps (H := H), f χ) +
        ∑ χ ∈ characterPairReps (H := H), f (-χ)) := by
      rw [Finset.sum_image (fun _ _ _ _ heq => neg_injective heq)]
    _ = _ := by rw [Finset.sum_add_distrib]

/-- Equation (9.2): the constant coefficient and a finite sum of cubic traces.
The expansion follows from orthogonality, not an assumed expansion hypothesis. -/
theorem indicator_cubicTrace_expansion [DecidableEq H]
    (hH : ∀ h : H, (3 : ℕ) • h = 0)
    (C : Finset H) (hC : InversionStable C) (h : H) :
    (if h ∈ C then (1 : ℂ) else 0) =
      (C.card : ℂ) / Fintype.card H +
        ∑ χ ∈ characterPairReps (H := H), indicatorFourierCoeff C χ * cubicTrace (χ h) := by
  rw [indicator_fourier_expansion, sum_character_pairs hH]
  simp only [indicatorFourierCoeff_zero, AddChar.zero_apply, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  rw [indicatorFourierCoeff_neg C hC, AddChar.neg_apply', ← mul_add, cubicTrace]

/-- Every selected character is nontrivial. -/
theorem characterPairReps_nontrivial (χ : AddChar H ℂ)
    (hχ : χ ∈ characterPairReps (H := H)) : χ ≠ 0 := by
  rintro rfl
  simp [characterPairReps] at hχ

/-- Equation (9.2) with exactly the positive-sum coefficient used in the paper. -/
theorem indicator_cubicTrace_expansion_positive [DecidableEq H]
    (hH : ∀ h : H, (3 : ℕ) • h = 0)
    (C : Finset H) (hC : InversionStable C) (h : H) :
    (if h ∈ C then (1 : ℂ) else 0) =
      (C.card : ℂ) / Fintype.card H +
        ∑ χ ∈ characterPairReps (H := H),
          ((∑ g ∈ C, χ g) / Fintype.card H) * cubicTrace (χ h) := by
  simpa only [indicatorFourierCoeff_eq_positive C hC] using
    indicator_cubicTrace_expansion hH C hC h

/-- The same expansion expressed with real scalar coefficients. -/
theorem indicator_cubicTrace_expansion_realCoeffs [DecidableEq H]
    (hH : ∀ h : H, (3 : ℕ) • h = 0)
    (C : Finset H) (hC : InversionStable C) (h : H) :
    (if h ∈ C then (1 : ℂ) else 0) =
      (C.card : ℂ) / Fintype.card H +
        ∑ χ ∈ characterPairReps (H := H),
          ((indicatorFourierCoeff C χ).re : ℂ) * cubicTrace (χ h) := by
  simpa only [indicatorFourierCoeff_re C hC] using
    indicator_cubicTrace_expansion hH C hC h

end ArtinMatthews
