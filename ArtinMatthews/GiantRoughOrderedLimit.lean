module

public import ArtinMatthews.GiantActualRoughSieve
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Ordered limits for the actual centered rough sums. The marking array
may depend on sieve depth, but is fixed before taking its x limsup. -/

namespace ArtinMatthews

open Filter
open scoped Topology

theorem giant_actual_centered_rough_limsup_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) (he : ∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5)
    (hinj : Function.Injective e) (ε c : ℝ) (m : ℕ)
    (hε : 0 < ε) (hεq : ε < 1 / 4) (hc : 0 < c) (hcε : c < ε / 2) (hm : 20000 ≤ m)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t)
    (hΦzero : Φ 0 = 0) :
    0 ≤ limsup (fun x : ℝ => Real.log x / (x * literalMarkedArrayMean e x) *
      |giantCenteredRoughSum e ε Φ T x (markedSieveExponent c m)|) atTop := by
  have hB := giant_actual_centered_rough_bound e he hinj ε c m hε hεq hc hcε hm
    Φ hT hΦ hderiv hΦT hΦ0 hΦzero (show (0 : ℝ) < 1 by norm_num)
  have hn : ∀ᶠ x : ℝ in atTop,
      0 ≤ Real.log x / (x * literalMarkedArrayMean e x) *
        |giantCenteredRoughSum e ε Φ T x (markedSieveExponent c m)| := by
    filter_upwards [literalMarkedArrayMean_lower_eventually e
      (fun i => lt_trans (by norm_num) (he i).1), eventually_gt_atTop (1 : ℝ)] with x hM hx
    have hm0 : 0 < literalMarkedArrayMean e x := lt_of_lt_of_le (by positivity) hM
    exact mul_nonneg (div_nonneg (Real.log_pos hx).le (mul_nonneg (by linarith) hm0.le))
      (abs_nonneg _)
  apply le_limsup_of_le (isBoundedUnder_of_eventually_le hB)
  intro b hb
  obtain ⟨x, hnx, hbx⟩ := (hn.and hb).exists
  exact hnx.trans hbx

/-- The x limit is taken first for each depth and its chosen finite array.
The number of bands and their locations may vary arbitrarily with depth. -/
theorem giant_actual_centered_rough_ordered_limit
    (K : ℕ → ℕ) (e : ∀ m, Fin (K m) → ℝ)
    (he : ∀ m i, (1 / 10 : ℝ) < e m i ∧ e m i < 1 / 5)
    (hinj : ∀ m, Function.Injective (e m)) (ε c : ℝ)
    (hε : 0 < ε) (hεq : ε < 1 / 4) (hc : 0 < c) (hcε : c < ε / 2)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t)
    (hΦzero : Φ 0 = 0) :
    Tendsto (fun m : ℕ => limsup (fun x : ℝ =>
      Real.log x / (x * literalMarkedArrayMean (e m) x) *
        |giantCenteredRoughSum (e m) ε Φ T x (markedSieveExponent c m)|) atTop)
      atTop (𝓝 0) := by
  have hb : ∀ᶠ m : ℕ in atTop,
      0 ≤ limsup (fun x : ℝ => Real.log x / (x * literalMarkedArrayMean (e m) x) *
        |giantCenteredRoughSum (e m) ε Φ T x (markedSieveExponent c m)|) atTop ∧
      limsup (fun x : ℝ => Real.log x / (x * literalMarkedArrayMean (e m) x) *
        |giantCenteredRoughSum (e m) ε Φ T x (markedSieveExponent c m)|) atTop ≤
          giantRoughSieveError Φ T c m := by
    filter_upwards [eventually_ge_atTop (20000 : ℕ)] with m hm
    exact ⟨giant_actual_centered_rough_limsup_nonneg (e m) (he m) (hinj m) ε c m
      hε hεq hc hcε hm Φ hT hΦ hderiv hΦT hΦ0 hΦzero,
      giant_actual_centered_rough_limsup (e m) (he m) (hinj m) ε c m
        hε hεq hc hcε hm Φ hT hΦ hderiv hΦT hΦ0 hΦzero⟩
  exact squeeze_zero' (hb.mono (fun _ h => h.1)) (hb.mono (fun _ h => h.2))
    (giantRoughSieveError_tendsto Φ T c)

end ArtinMatthews
