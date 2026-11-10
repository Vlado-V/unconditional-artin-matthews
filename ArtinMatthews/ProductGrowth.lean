module

public import ArtinMatthews.Index
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! An explicit quadratic bound on the logarithm of the exceptional product. -/

namespace ArtinMatthews

lemma factor_natAbs_le {a : ℤ} (ha : 2 ≤ a.natAbs) {j : ℕ} (_hj : 1 ≤ j) :
    (a ^ j - 1).natAbs ≤ 2 * a.natAbs ^ j := by
  have h := Int.natAbs_sub_le (a ^ j) 1
  rw [Int.natAbs_pow] at h
  have hp : 1 ≤ a.natAbs ^ j := one_le_pow₀ (by omega)
  norm_num at h
  omega

lemma log_factor_le {a : ℤ} (ha : 2 ≤ a.natAbs) {j : ℕ} (hj : 1 ≤ j) :
    Real.log ((a ^ j - 1).natAbs : ℝ) ≤
      Real.log 2 + (j : ℝ) * Real.log (a.natAbs : ℝ) := by
  have hpos : 0 < (a ^ j - 1).natAbs :=
    Int.natAbs_pos.mpr (pow_sub_one_ne_zero ha hj)
  have ha0 : (a.natAbs : ℝ) ≠ 0 := by exact_mod_cast (by omega : a.natAbs ≠ 0)
  calc
    Real.log ((a ^ j - 1).natAbs : ℝ) ≤ Real.log (2 * (a.natAbs : ℝ) ^ j) := by
      apply Real.log_le_log (by exact_mod_cast hpos)
      exact_mod_cast factor_natAbs_le ha hj
    _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ ha0), Real.log_pow]

/-- A fixed constant depending only on the integer bases. -/
noncomputable def productGrowthConstant (S : Finset ℤ) : ℝ :=
  ∑ a ∈ S, (Real.log 2 + Real.log (a.natAbs : ℝ))

lemma productGrowthConstant_pos {S : Finset ℤ} (hS : AdmissibleBases S) :
    0 < productGrowthConstant S := by
  apply Finset.sum_pos
  · intro a ha
    have h := natAbs_ge_two_of_admissible hS ha
    have hp : 1 < (a.natAbs : ℝ) := by exact_mod_cast (by omega : 1 < a.natAbs)
    exact add_pos (Real.log_pos (by norm_num)) (Real.log_pos hp)
  · exact hS.1

lemma log_exceptionalProduct_eq {S : Finset ℤ} (hS : AdmissibleBases S) (m : ℕ) :
    Real.log (exceptionalProduct S m : ℝ) =
      ∑ a ∈ S, ∑ j ∈ Finset.Icc 1 m, Real.log ((a ^ j - 1).natAbs : ℝ) := by
  unfold exceptionalProduct
  push_cast
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro a ha
    apply Real.log_prod
    intro j hj
    exact_mod_cast (Int.natAbs_pos.mpr
      (pow_sub_one_ne_zero (natAbs_ge_two_of_admissible hS ha) (Finset.mem_Icc.mp hj).1)).ne'
  · intro a ha
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact_mod_cast (Int.natAbs_pos.mpr
      (pow_sub_one_ne_zero (natAbs_ge_two_of_admissible hS ha) (Finset.mem_Icc.mp hj).1)).ne'

/-- The constant is independent of the exponent cutoff. -/
theorem log_exceptionalProduct_le {S : Finset ℤ} (hS : AdmissibleBases S)
    {m : ℕ} (hm : 1 ≤ m) :
    Real.log (exceptionalProduct S m : ℝ) ≤ productGrowthConstant S * (m : ℝ) ^ 2 := by
  rw [log_exceptionalProduct_eq hS]
  calc
    (∑ a ∈ S, ∑ j ∈ Finset.Icc 1 m, Real.log ((a ^ j - 1).natAbs : ℝ)) ≤
        ∑ a ∈ S, ∑ _j ∈ Finset.Icc 1 m,
          (m : ℝ) * (Real.log 2 + Real.log (a.natAbs : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro j hj
      have habs := natAbs_ge_two_of_admissible hS ha
      have hlog : 0 ≤ Real.log (a.natAbs : ℝ) := Real.log_natCast_nonneg _
      have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hj' : (j : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hj).2
      calc
        _ ≤ Real.log 2 + (j : ℝ) * Real.log (a.natAbs : ℝ) :=
          log_factor_le habs (Finset.mem_Icc.mp hj).1
        _ ≤ (m : ℝ) * (Real.log 2 + Real.log (a.natAbs : ℝ)) := by nlinarith
    _ = productGrowthConstant S * (m : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      unfold productGrowthConstant
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring

end ArtinMatthews
