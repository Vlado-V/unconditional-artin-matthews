module

public import ArtinMatthews.GiantPrime
public import ArtinMatthews.MarkedEstimateMertensBandCore
public import ArtinMatthews.MarkedEstimateMertensBands
public import Mathlib.NumberTheory.Chebyshev
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# The giant-prime window and its normalization

These definitions give the finite window and reciprocal sum of (1.2). The
limit in (1.3) follows from the actual Mertens theorem, including the open
lower and closed upper endpoints of the prime interval.
-/

namespace ArtinMatthews

open Filter
open scoped BigOperators

noncomputable def giantPrimeWindow (x ε : ℝ) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊x ^ (1 - ε / 2)⌋₊).filter
    (fun p : ℕ => x ^ (1 - ε) < (p : ℝ))

theorem mem_giantPrimeWindow {p : ℕ} {x ε : ℝ} (hx : 0 ≤ x) :
    p ∈ giantPrimeWindow x ε ↔ p.Prime ∧
      x ^ (1 - ε) < (p : ℝ) ∧ (p : ℝ) ≤ x ^ (1 - ε / 2) := by
  classical
  simp only [giantPrimeWindow, Finset.mem_filter, Nat.mem_primesLE,
    Nat.le_floor_iff (Real.rpow_nonneg hx _)]
  tauto

/-- The finite divisor statistic agrees with the window sum of (1.2). -/
theorem giantPrimeFactors_eq_window_filter {n : ℕ} (hn : n ≠ 0)
    {x ε : ℝ} (hx : 0 ≤ x) :
    giantPrimeFactors n x ε = (giantPrimeWindow x ε).filter (fun p => p ∣ n) := by
  classical
  ext p
  simp only [giantPrimeFactors, Finset.mem_filter, mem_primeFactorsAbove,
    mem_giantPrimeWindow hx]
  tauto

noncomputable def giantPrimeReciprocalSum (x ε : ℝ) : ℝ :=
  ∑ p ∈ giantPrimeWindow x ε, (1 : ℝ) / p

noncomputable def giantPrimeConstant (ε : ℝ) : ℝ :=
  Real.log ((1 - ε / 2) / (1 - ε))

/-- Mertens' theorem for an open-closed interval with fixed positive powers. -/
theorem prime_reciprocal_power_interval_tendsto {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => markedOpenBandMass (x ^ a) (x ^ b))
      atTop (nhds (Real.log (b / a))) := by
  have hb : 0 < b := ha.trans_le hab
  have hE := (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have hEa := hE.comp (tendsto_rpow_atTop ha)
  have hEb := hE.comp (tendsto_rpow_atTop hb)
  have h := (hEb.sub hEa).const_add (Real.log (b / a))
  simp only [sub_self, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [markedOpenBandMass_eq_sub (Real.rpow_nonneg hx0.le _)
    (Real.rpow_le_rpow_of_exponent_le hx.le hab),
    markedPrimePrefix_eq_mertens, markedPrimePrefix_eq_mertens,
    Real.log_rpow hx0, Real.log_rpow hx0,
    Real.log_mul hb.ne' hlx, Real.log_mul ha.ne' hlx,
    Real.log_div hb.ne' ha.ne']
  simp only [Function.comp_apply]
  ring

/-- The normalization in (1.3), proved without a prime-distribution hypothesis. -/
theorem giantPrimeReciprocalSum_tendsto {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun x : ℝ => giantPrimeReciprocalSum x ε)
      atTop (nhds (giantPrimeConstant ε)) := by
  exact prime_reciprocal_power_interval_tendsto (by linarith) (by linarith)

theorem giantPrimeConstant_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    0 < giantPrimeConstant ε := by
  apply Real.log_pos
  apply (one_lt_div (by linarith : 0 < 1 - ε)).mpr
  linarith

end ArtinMatthews
