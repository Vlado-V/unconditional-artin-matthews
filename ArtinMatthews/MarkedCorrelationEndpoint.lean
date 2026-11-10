module

public import ArtinMatthews.MarkedCorrelationLimit
public import ArtinMatthews.MarkedCorrelationNormalization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The exact correlation endpoint after the ordered finite-array limits.
The single-array marked estimate remains an explicit analytic input. -/

namespace ArtinMatthews

open Filter
open scoped Topology

theorem marked_actual_correlation_isLittleO_of_marked
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
    markedPrimeCorrelation Φ T F =o[atTop] (fun x : ℝ => x / Real.log x) := by
  apply marked_correlation_isLittleO_of_normalized_norm
  exact marked_actual_correlation_norm_tendsto_of_marked
    Φ hT ha hΦ hderiv hΦT hΦ0 hlow F hC hF c A n₀ hmarked

end ArtinMatthews
