module

public import ArtinMatthews.KummerSplittingDegree
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-!
# The actual varying-exponent Kummer field is a splitting field

The concrete two-generator field is identified with the root-set adjoin of
`(X^q - 1) (X^q - a)`. Thus normality and finite-dimensionality concern the
actual field used in the degree and discriminant calculations.
-/

open Polynomial

namespace ArtinMatthews

noncomputable def primeKummerPolynomial (q : ℕ) (a : ℤ) : ℚ[X] :=
  (X ^ q - 1) * (X ^ q - C (a : ℚ))

theorem primeKummerPolynomial_ne_zero {q : ℕ} (hq : 0 < q) (a : ℤ) :
    primeKummerPolynomial q a ≠ 0 := by
  apply mul_ne_zero
  · simpa only [map_one] using X_pow_sub_C_ne_zero hq (1 : ℚ)
  · exact X_pow_sub_C_ne_zero hq (a : ℚ)

theorem mem_primeKummerPolynomial_rootSet_iff {q : ℕ} (hq : 0 < q)
    (a : ℤ) (z : ℂ) :
    z ∈ (primeKummerPolynomial q a).rootSet ℂ ↔
      z ^ q = 1 ∨ z ^ q = (a : ℂ) := by
  rw [Polynomial.mem_rootSet_of_ne (primeKummerPolynomial_ne_zero hq a)]
  simp [primeKummerPolynomial, sub_eq_zero]

theorem primeCyclotomicField_le_primeKummerField (q : ℕ) (a : ℤ) :
    primeCyclotomicField q ≤ primeKummerField q a := by
  rw [primeKummerField_eq_adjoin, primeCyclotomicField]
  rw [IntermediateField.adjoin_le_iff]
  intro z hz
  exact IntermediateField.subset_adjoin ℚ _ (Or.inl hz)

theorem primeRadicalRoot_mem_primeKummerField (q : ℕ) (a : ℤ) :
    primeRadicalRoot q a ∈ primeKummerField q a := by
  rw [primeKummerField_eq_adjoin]
  exact IntermediateField.subset_adjoin ℚ _ (Or.inr (Set.mem_singleton _))

theorem radical_mem_primeKummerField {q : ℕ} (hq : 0 < q) {a : ℤ}
    (ha : a ≠ 0) {z : ℂ} (hz : z ^ q = (a : ℂ)) :
    z ∈ primeKummerField q a := by
  have hα : primeRadicalRoot q a ≠ 0 := primeRadicalRoot_ne_zero hq ha
  have hdiv : (z / primeRadicalRoot q a) ^ q = 1 := by
    rw [div_pow, hz, primeRadicalRoot_pow hq]
    exact div_self (by exact_mod_cast ha)
  have hmem : z / primeRadicalRoot q a ∈ primeKummerField q a :=
    primeCyclotomicField_le_primeKummerField q a
      (root_of_unity_mem_primeCyclotomicField hq hdiv)
  simpa only [div_mul_cancel₀ _ hα] using
    (primeKummerField q a).mul_mem hmem (primeRadicalRoot_mem_primeKummerField q a)

theorem primeKummerField_eq_adjoin_rootSet {q : ℕ} (hq : 0 < q)
    {a : ℤ} (ha : a ≠ 0) :
    primeKummerField q a =
      IntermediateField.adjoin ℚ ((primeKummerPolynomial q a).rootSet ℂ) := by
  apply le_antisymm
  · rw [primeKummerField_eq_adjoin, IntermediateField.adjoin_le_iff]
    intro z hz
    apply IntermediateField.subset_adjoin
    apply (mem_primeKummerPolynomial_rootSet_iff hq a z).mpr
    rcases hz with hz | hz
    · exact Or.inl ((Set.mem_singleton_iff.mp hz) ▸ primeCyclotomicRoot_pow hq)
    · exact Or.inr ((Set.mem_singleton_iff.mp hz) ▸ primeRadicalRoot_pow hq a)
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rcases (mem_primeKummerPolynomial_rootSet_iff hq a z).mp hz with hz | hz
    · exact primeCyclotomicField_le_primeKummerField q a
        (root_of_unity_mem_primeCyclotomicField hq hz)
    · exact radical_mem_primeKummerField hq ha hz

noncomputable instance primeKummerField_isSplittingField (q : ℕ) (a : ℤ)
    [NeZero q] [NeZero a] :
    IsSplittingField ℚ (primeKummerField q a) (primeKummerPolynomial q a) := by
  rw [primeKummerField_eq_adjoin_rootSet (NeZero.pos q) (NeZero.ne a)]
  exact IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

noncomputable instance primeKummerField_finiteDimensional (q : ℕ) (a : ℤ)
    [NeZero q] [NeZero a] : FiniteDimensional ℚ (primeKummerField q a) :=
  IsSplittingField.finiteDimensional (primeKummerField q a) (primeKummerPolynomial q a)

noncomputable instance primeKummerField_normal (q : ℕ) (a : ℤ)
    [NeZero q] [NeZero a] : Normal ℚ (primeKummerField q a) :=
  Normal.of_isSplittingField (primeKummerPolynomial q a)

noncomputable instance primeKummerField_isGalois (q : ℕ) (a : ℤ)
    [NeZero q] [NeZero a] : IsGalois ℚ (primeKummerField q a) where

noncomputable instance primeKummerField_numberField_of_neZero (q : ℕ) (a : ℤ)
    [NeZero q] [NeZero a] : NumberField (primeKummerField q a) where

end ArtinMatthews
