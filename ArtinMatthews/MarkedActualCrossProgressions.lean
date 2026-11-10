module

public import ArtinMatthews.MarkedActualMomentProgressions
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

/-! The cross-array progression estimate. Distinct arrays use the full
product of first moments; repeated arrays use the separate second-moment
result, retaining all coincident represented selections. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Asymptotics Topology

theorem marked_actual_cross_moment_progressions {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι → ℝ) (f : κ → ℝ)
    (he : ∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5)
    (hf : ∀ j, (1 / 10 : ℝ) < f j ∧ f j < 1 / 5)
    (hinj : Function.Injective (Sum.elim e f)) (c A : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (fun x : ℝ => markedProgressionDiscrepancy
      (fun u => divisorWeight Finset.univ (fun i => markedLogPowerBand (e i) x)
          (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) u *
        divisorWeight Finset.univ (fun j => markedLogPowerBand (f j) x)
          (fun j => bandReciprocalMass (markedLogPowerBand (f j) x)) u)
      (independentArrayMean (fun i => markedLogPowerBand (e i) x)
          (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) *
        independentArrayMean (fun j => markedLogPowerBand (f j) x)
          (fun j => bandReciprocalMass (markedLogPowerBand (f j) x))) Φ T x ⌊x ^ c⌋₊) =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have hrange : ∀ z, (1 / 10 : ℝ) < Sum.elim e f z ∧ Sum.elim e f z < 1 / 5 := by
    intro z
    cases z with
    | inl i => exact he i
    | inr j => exact hf j
  have h := marked_actual_first_moment_progressions (Sum.elim e f) hrange hinj c A hc0 hc1
    Φ hT hΦ hderiv hΦT hΦ0
  simpa only [markedProgressionDiscrepancy, divisorWeight, independentArrayMean_eq, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr] using h

end ArtinMatthews
