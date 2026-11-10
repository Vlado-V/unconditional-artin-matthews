module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.Bounds
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

/-! Removing the coprimality restriction in marked progression main terms.
The loss is controlled by the reciprocal mass of the prime factors of the
represented divisor. The multiple sum is reindexed exactly before applying
any bound. -/

namespace ArtinMatthews

open scoped BigOperators

lemma reciprocal_Icc_eq_harmonic (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, 1 / (r : ℝ)) = (harmonic R : ℝ) := by
  simp [harmonic_eq_sum_Icc, one_div]

/-- Exact reciprocal mass of multiples of a positive integer in `[1,R]`. -/
theorem reciprocal_multiples_eq (R p : ℕ) (hp : 0 < p) :
    (∑ r ∈ (Finset.Icc 1 R).filter (p ∣ ·), 1 / (r : ℝ)) =
      (1 / (p : ℝ)) * (harmonic (R / p) : ℝ) := by
  classical
  rw [← reciprocal_Icc_eq_harmonic, Finset.mul_sum]
  apply Finset.sum_bij (fun r _ => r / p)
  · intro r hr
    obtain ⟨hrI, hpr⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr1, hrR⟩ := Finset.mem_Icc.mp hrI
    have hmul := Nat.mul_div_cancel' hpr
    have hpos : 0 < r / p := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz, mul_zero] at hmul
      omega
    exact Finset.mem_Icc.mpr ⟨hpos, Nat.div_le_div_right hrR⟩
  · intro a ha b hb hab
    have hpa := (Finset.mem_filter.mp ha).2
    have hpb := (Finset.mem_filter.mp hb).2
    calc
      a = p * (a / p) := (Nat.mul_div_cancel' hpa).symm
      _ = p * (b / p) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hpb
  · intro k hk
    obtain ⟨hk1, hkR⟩ := Finset.mem_Icc.mp hk
    refine ⟨p * k, ?_, Nat.mul_div_cancel_left k hp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hp (by omega)), ?_⟩, dvd_mul_right p k⟩
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le hp).mp hkR
  · intro r hr
    have hpr := (Finset.mem_filter.mp hr).2
    rw [one_div_mul_one_div, ← Nat.cast_mul, Nat.mul_div_cancel' hpr]

/-- Each fixed divisibility condition costs at most its reciprocal density
multiplied by the full harmonic mass. -/
theorem reciprocal_multiples_le (R p : ℕ) (hp : 0 < p) :
    (∑ r ∈ (Finset.Icc 1 R).filter (p ∣ ·), 1 / (r : ℝ)) ≤
      (1 / (p : ℝ)) * (harmonic R : ℝ) := by
  rw [reciprocal_multiples_eq R p hp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← reciprocal_Icc_eq_harmonic, ← reciprocal_Icc_eq_harmonic]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨hk1, hkR⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hk1, hkR.trans (Nat.div_le_self R p)⟩
  · intro k _ _
    positivity

/-- Shared-prime union bound for the harmonic mass of noncoprime moduli. -/
theorem noncoprime_reciprocal_sum_le_harmonic (R d : ℕ) (hd : 0 < d) :
    (∑ r ∈ (Finset.Icc 1 R).filter (fun r => ¬d.Coprime r), 1 / (r : ℝ)) ≤
      (harmonic R : ℝ) * ∑ p ∈ d.primeFactors, 1 / (p : ℝ) := by
  classical
  let F : ℕ → ℝ := fun r => ∑ p ∈ d.primeFactors,
    if p ∣ r then 1 / (r : ℝ) else 0
  calc
    _ ≤ ∑ r ∈ (Finset.Icc 1 R).filter (fun r => ¬d.Coprime r), F r := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨p, hp, hpd, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp
        (Finset.mem_filter.mp hr).2
      have hpF : p ∈ d.primeFactors := hp.mem_primeFactors hpd (by omega)
      have hsingle := Finset.single_le_sum
        (s := d.primeFactors) (f := fun q => if q ∣ r then 1 / (r : ℝ) else 0)
        (fun q _ => by split_ifs <;> positivity) hpF
      simpa [F, hpr] using hsingle
    _ ≤ ∑ r ∈ Finset.Icc 1 R, F r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro r _ _
      change 0 ≤ ∑ p ∈ d.primeFactors, if p ∣ r then 1 / (r : ℝ) else 0
      exact Finset.sum_nonneg fun p _ => by split_ifs <;> positivity
    _ = ∑ p ∈ d.primeFactors,
          ∑ r ∈ (Finset.Icc 1 R).filter (p ∣ ·), 1 / (r : ℝ) := by
      dsimp only [F]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_filter]
    _ ≤ ∑ p ∈ d.primeFactors, (1 / (p : ℝ)) * (harmonic R : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact reciprocal_multiples_le R p (Nat.pos_of_mem_primeFactors hp)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- The logarithmic form used when summing the progression errors. -/
theorem noncoprime_reciprocal_sum_le_log (R d : ℕ) (hd : 0 < d) :
    (∑ r ∈ (Finset.Icc 1 R).filter (fun r => ¬d.Coprime r), 1 / (r : ℝ)) ≤
      (1 + Real.log R) * ∑ p ∈ d.primeFactors, 1 / (p : ℝ) := by
  apply (noncoprime_reciprocal_sum_le_harmonic R d hd).trans
  apply mul_le_mul_of_nonneg_right (harmonic_le_one_add_log R)
  positivity

end ArtinMatthews
