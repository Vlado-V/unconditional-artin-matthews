module

public import ArtinMatthews.ShiftedConvolutionParseval
public import Mathlib.Analysis.Fourier.ZMod


set_option backward.privateInPublic true
@[expose] public section

/-!
# The literal congruence-constrained convolution in (5.6)

The frequency is `m4*k2 - m3*k1`; the congruence is
`m3²*k1 = m4²*k2 (mod D)`. Its expansion is a normalized character average,
so the coefficient-energy bound has no loss depending on D.
-/

noncomputable section
open Complex MeasureTheory AddCircle Finset
open scoped BigOperators

namespace ArtinMatthews

/-- The exact coefficient sequence used after the two Voronoi transformations. -/
def shiftedConvolutionCoeff (S T : Finset ℕ) (m3 m4 D : ℕ)
    (a b : ℕ → ℂ) (r : ℤ) : ℂ :=
  ∑ k1 ∈ S, ∑ k2 ∈ T,
    if (m4 : ℤ) * k2 - (m3 : ℤ) * k1 = r ∧
        (m3 ^ 2 * k1 : ZMod D) = (m4 ^ 2 * k2 : ZMod D)
    then a k1 * b k2 else 0

/-- The first polynomial for one character in the normalized congruence expansion. -/
def shiftedConvolutionLeft (S : Finset ℕ) (m3 D : ℕ) [NeZero D]
    (a : ℕ → ℂ) (j : ZMod D) : C(AddCircle (1 : ℝ), ℂ) :=
  shiftedTrigPolynomial S (fun k ↦ a k * ZMod.stdAddChar (j * (m3 ^ 2 * k : ZMod D)))
    (fun k ↦ -(m3 : ℤ) * k)

/-- The second polynomial has positive frequencies and the opposite congruence character. -/
def shiftedConvolutionRight (T : Finset ℕ) (m4 D : ℕ) [NeZero D]
    (b : ℕ → ℂ) (j : ZMod D) : C(AddCircle (1 : ℝ), ℂ) :=
  shiftedTrigPolynomial T (fun k ↦ b k * ZMod.stdAddChar (-(j * (m4 ^ 2 * k : ZMod D))))
    (fun k ↦ (m4 : ℤ) * k)

/-- Exact expansion of the congruence constraint, with normalization 1/D. -/
theorem shiftedConvolutionCoeff_eq_average (S T : Finset ℕ) (m3 m4 D : ℕ) [NeZero D]
    (a b : ℕ → ℂ) (r : ℤ) :
    shiftedConvolutionCoeff S T m3 m4 D a b r =
      (∑ j : ZMod D, fourierCoeff
        (shiftedConvolutionLeft S m3 D a j * shiftedConvolutionRight T m4 D b j) r) / D := by
  have hD : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne D)
  simp only [shiftedConvolutionLeft, shiftedConvolutionRight, fourierCoeff_shiftedTrigProduct]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := T)]
  rw [Finset.sum_div]
  unfold shiftedConvolutionCoeff
  apply Finset.sum_congr rfl
  intro k1 _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k2 _
  have hfreq : -(m3 : ℤ) * k1 + (m4 : ℤ) * k2 = (m4 : ℤ) * k2 - (m3 : ℤ) * k1 := by ring
  rw [hfreq]
  by_cases hr : (m4 : ℤ) * k2 - (m3 : ℤ) * k1 = r
  · simp only [hr, true_and, ite_true]
    have hprod (j : ZMod D) :
        (a k1 * ZMod.stdAddChar (j * (m3 ^ 2 * k1 : ZMod D))) *
          (b k2 * ZMod.stdAddChar (-(j * (m4 ^ 2 * k2 : ZMod D)))) =
        (a k1 * b k2) * ZMod.stdAddChar
          (j * ((m3 ^ 2 * k1 : ZMod D) - (m4 ^ 2 * k2 : ZMod D))) := by
      rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    simp_rw [hprod]
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar D)]
    simp only [ZMod.card, sub_eq_zero]
    split_ifs <;> simp_all
  · simp [hr]

/-- Each character component obeys the same coefficient-energy bound. -/
theorem shiftedConvolution_component_energy_le (S T : Finset ℕ) (m3 m4 D : ℕ)
    [NeZero D] (hm4 : 0 < m4) (a b : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hleft : ∀ (j : ZMod D) (x : AddCircle (1 : ℝ)),
      ‖shiftedConvolutionLeft S m3 D a j x‖ ≤ C) (j : ZMod D) (R : Finset ℤ) :
    ∑ r ∈ R, ‖fourierCoeff
      (shiftedConvolutionLeft S m3 D a j * shiftedConvolutionRight T m4 D b j) r‖ ^ 2 ≤
        C ^ 2 * ∑ k ∈ T, ‖b k‖ ^ 2 := by
  have hinj : Set.InjOn (fun k : ℕ ↦ (m4 : ℤ) * k) T := by
    intro k hk l hl he
    have hm : (m4 : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm4)
    exact_mod_cast (mul_left_cancel₀ hm he)
  have hp := shiftedPolynomial_product_energy_le T
    (fun k ↦ b k * ZMod.stdAddChar (-(j * (m4 ^ 2 * k : ZMod D))))
    (fun k ↦ (m4 : ℤ) * k) hinj (shiftedConvolutionLeft S m3 D a j) C hC (hleft j) R
  simpa only [shiftedConvolutionRight, norm_mul, AddChar.norm_apply, mul_one] using hp

/-- The exact (5.6) energy reduction. The normalized D-character average
costs no factor of D. Coprimality is not needed for this analytic bound. -/
theorem shiftedConvolution_energy_le (S T : Finset ℕ) (m3 m4 D : ℕ)
    [NeZero D] (hm4 : 0 < m4) (a b : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hleft : ∀ (j : ZMod D) (x : AddCircle (1 : ℝ)),
      ‖shiftedConvolutionLeft S m3 D a j x‖ ≤ C) (R : Finset ℤ) :
    ∑ r ∈ R, ‖shiftedConvolutionCoeff S T m3 m4 D a b r‖ ^ 2 ≤
      C ^ 2 * ∑ k ∈ T, ‖b k‖ ^ 2 := by
  have havg := normalized_average_energy_le (Finset.univ : Finset (ZMod D)) R
    Finset.univ_nonempty
    (fun j r ↦ fourierCoeff
      (shiftedConvolutionLeft S m3 D a j * shiftedConvolutionRight T m4 D b j) r)
    (C ^ 2 * ∑ k ∈ T, ‖b k‖ ^ 2)
    (fun j _ ↦ shiftedConvolution_component_energy_le S T m3 m4 D hm4 a b C hC hleft j R)
  simpa only [Finset.card_univ, ZMod.card, ← shiftedConvolutionCoeff_eq_average] using havg

end ArtinMatthews
