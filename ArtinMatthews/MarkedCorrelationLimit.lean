module

public import ArtinMatthews.MarkedOrderedLimits
public import ArtinMatthews.MarkedActualDeweighting
public import ArtinMatthews.MarkedArrayExistence
public import ArtinMatthews.MarkedCorrelationAveraging
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Discharged finite-array and ordered-limit assembly for Theorem 8.2.
The remaining input is explicitly the single-array marked correlation bound. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

noncomputable def markedPrimeCorrelation (Φ : ℝ → ℝ) (T : ℝ)
    (F : ℝ → ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime),
    (Φ ((u : ℝ) / x) : ℂ) * F x u

noncomputable def markedPrimeSingleArrayCorrelation {I : Type*}
    [Fintype I] [DecidableEq I] (e : I → ℝ) (Φ : ℝ → ℝ) (T : ℝ)
    (F : ℝ → ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime),
    (Φ ((u : ℝ) / x) : ℂ) * F x u *
      ((divisorWeight Finset.univ (fun i => markedLogPowerBand (e i) x)
        (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) u /
          independentArrayMean (fun i => markedLogPowerBand (e i) x)
            (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) : ℝ) : ℂ)

/-- The unmarked correlation vanishes once the exact uniform single-array
marked bound is supplied. The number of bands may depend on the fixed even
depth; every use of an array occurs before taking the limit in `x`. -/
theorem marked_actual_correlation_norm_tendsto_of_marked
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0)
    (F : ℝ → ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᶠ x : ℝ in atTop, ∀ u, (u + 1).Prime → ‖F x u‖ ≤ C)
    (c A : ℝ) (n₀ : ℕ)
    (hmarked : ∀ n ≥ n₀, ∃ K : ℕ, ∀ e : Fin K → ℝ,
      (∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5) → Function.Injective e →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
        Real.log x / x * ‖markedPrimeSingleArrayCorrelation e Φ T F x‖ ≤
          A * Real.exp (-(2 * (n : ℝ))) /
            (markedCorrelationSieveExponent c (2 * n)) ^ 2 + ε) :
    Tendsto (fun x => Real.log x / x * ‖markedPrimeCorrelation Φ T F x‖) atTop (𝓝 0) := by
  apply marked_ordered_auxiliary_limits _ c A n₀
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (div_nonneg (Real.log_pos hx).le (by linarith)) (norm_nonneg _)
  · intro n hn
    obtain ⟨K, hK⟩ := hmarked n hn
    let D := C * markedPrimeDeweightingConstant K (1 / 960048) 20000 Φ T
    refine ⟨D, ?_⟩
    intro B hB ε hε
    obtain ⟨e, he, hinj⟩ := exists_marked_disjoint_arrays B K
    have hB' : 0 < Fintype.card (Fin B) := by simpa using hB
    have hde := marked_actual_prime_deweighting_canonical e he hinj hB'
      Φ hT ha hΦ hderiv hΦT hΦ0 hlow F hC hF
    have hmarks : ∀ᶠ x : ℝ in atTop, ∀ j : Fin B,
        Real.log x / x * ‖markedPrimeSingleArrayCorrelation (e j) Φ T F x‖ ≤
          A * Real.exp (-(2 * (n : ℝ))) /
            (markedCorrelationSieveExponent c (2 * n)) ^ 2 + ε := by
      rw [Filter.eventually_all]
      intro j
      apply hK (e j) (he j) _ ε hε
      intro i k hik
      exact (Prod.mk.inj (hinj hik)).2
    filter_upwards [hde, hmarks, eventually_gt_atTop (1 : ℝ)] with x hd hm hx
    let S := (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime)
    let w (u : ℕ) := (Φ ((u : ℝ) / x) : ℂ) * F x u
    let z (j : Fin B) (u : ℕ) :=
      divisorWeight Finset.univ (fun i => markedLogPowerBand (e j i) x)
        (fun i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u /
          independentArrayMean (fun i => markedLogPowerBand (e j i) x)
            (fun i => bandReciprocalMass (markedLogPowerBand (e j i) x))
    have hs : 0 ≤ Real.log x / x := div_nonneg (Real.log_pos hx).le (by linarith)
    have hdn : Real.log x / x *
        ‖∑ u ∈ S, w u * (((∑ j, z j u) / Fintype.card (Fin B) - 1 : ℝ) : ℂ)‖ ≤
          D / Real.sqrt B := by
      have hh := mul_le_mul_of_nonneg_left hd hs
      convert hh using 1
      · rfl
      · simp only [Fintype.card_fin]
        dsimp [D]
        field_simp [(Real.log_pos hx).ne', (show (0 : ℝ) < x by linarith).ne']
    have h := marked_scaled_average_bound S w z hB' hs hm hdn
    change Real.log x / x * ‖markedPrimeCorrelation Φ T F x‖ ≤ _ at h
    linarith

end ArtinMatthews
