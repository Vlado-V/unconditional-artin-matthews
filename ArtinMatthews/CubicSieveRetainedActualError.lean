module

public import ArtinMatthews.CubicSieveRetainedError
public import ArtinMatthews.CubicSamplingSourceTruncation
public import ArtinMatthews.CubicSieveTestVariation
public import ArtinMatthews.HeckePrimeLogSaving
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original retained marking coefficients and correction levels
leave a genuine power saving in the divisor-progression remainder. -/

noncomputable section
namespace ArtinMatthews

open Filter Finset
open scoped BigOperators ContDiff Topology

theorem cubicSieve_retainedActual_error_log_saving {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j ∧ e j ≤ 1 / 5) (hinj : Function.Injective e)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    {γ : ℝ} (hγ : 0 < γ) (m : ℕ) (hlevel : γ * (8 * (m : ℝ) + 2) ≤ 1 / 16) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let P := fun j => markedLogPowerBand (e j) x
      let V := fun j => bandReciprocalMass (P j)
      let k := cubicSamplingTruncationDepth x
      |cubicSieveRetainedWeightedSum P V Φ (x ^ γ) x m k -
        cubicSieveRetainedProgressionModel P V Φ (x ^ γ) x m k| ≤ x * (Real.log x) ^ (-A) := by
  obtain ⟨C, hC, hvariation⟩ := cubicSieve_shiftedTest_variation_bound Φ hΦ
  let K := 68 * Real.sqrt 3 * C
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have htr := cubicSampling_actualArray_retained_eventually e he hinj (fun _ => 1)
    (fun _ => by norm_num) (by norm_num : (0 : ℝ) < 1 / 16)
  have hsmall := heckePrime_uniform_power_log_saving K (3 / 4) 1 A hK (by norm_num) zero_lt_one
  filter_upwards [htr, hsmall, eventually_gt_atTop (1 : ℝ)] with x hxtr hxsmall hx₁
  dsimp only at hxtr ⊢
  let P := fun j => markedLogPowerBand (e j) x
  let V := fun j => bandReciprocalMass (P j)
  let k := cubicSamplingTruncationDepth x
  let D := x ^ (1 / 16 : ℝ)
  let R := ⌊D⌋₊
  have hx₀ := zero_lt_one.trans hx₁
  have hD : 0 < D := Real.rpow_pos_of_pos hx₀ _
  have hR : (R : ℝ) ≤ D := Nat.floor_le hD.le
  have hrange : ∀ S ∈ (Nat.primesLE ⌊x ^ γ⌋₊).powerset,
      cubicSieveCorrectionCoeff (x ^ γ) m S ≠ 0 → roughSubsetDivisor S ≤ R := by
    intro S hS hne
    apply Nat.le_floor
    exact (cubicSieve_correctionCoeff_level (Real.one_lt_rpow hx₁ hγ) (mem_powerset.mp hS) hne).2.2.trans
      ((by rw [← Real.rpow_mul hx₀.le] : (x ^ γ) ^ (8 * (m : ℝ) + 2) = x ^ (γ * (8 * (m : ℝ) + 2))).le.trans
        (Real.rpow_le_rpow_of_exponent_le hx₁.le hlevel))
  have hD2 : D ^ 2 = x ^ (1 / 8 : ℝ) := by
    dsimp only [D]
    rw [← Real.rpow_natCast (x ^ (1 / 16 : ℝ)) 2, ← Real.rpow_mul hx₀.le]
    norm_num
  have hD4 : D ^ 2 * D ^ 2 = x ^ (1 / 4 : ℝ) := by
    rw [hD2, ← Real.rpow_add hx₀]
    norm_num
  have hlev : D ^ 2 * (R : ℝ) ^ 2 ≤ x := by
    calc
      _ ≤ D ^ 2 * D ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hR 2) (sq_nonneg D)
      _ = x ^ (1 / 4 : ℝ) := hD4
      _ ≤ x := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx₁.le (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hbound := cubicSieve_retainedProgression_error P V Φ hΦ hs hx₁.le m k R hD.le hrange
    (fun t ht i hi => ⟨(hxtr.2.1 t ht i hi).1, (hxtr.2.1 t ht i hi).2.2⟩) hxtr.2.2 hlev
  refine hbound.trans (le_trans ?_ (hxsmall x (by rw [Real.rpow_one])))
  calc
    _ ≤ 68 * Real.sqrt (3 * x) * C * D ^ 2 * D ^ 2 := by
      gcongr
      exact hvariation x hx₁.le
    _ = K * x ^ (3 / 4 : ℝ) := by
      rw [mul_assoc (68 * Real.sqrt (3 * x) * C), hD4,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_eq_rpow x]
      dsimp only [K]
      rw [show (3 / 4 : ℝ) = 1 / 2 + 1 / 4 by norm_num, Real.rpow_add hx₀]
      ring

end ArtinMatthews
