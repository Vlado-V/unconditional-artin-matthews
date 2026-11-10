module

public import ArtinMatthews.MarkedEstimateArrayModel
public import ArtinMatthews.MarkedEstimateMertensBandCore
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.MarkedActualArrayProgressions
public import ArtinMatthews.MarkedArrayMean
public import ArtinMatthews.MarkedEstimateActualModel
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

/-! The first and second actual marking-array progression estimates with
the previously constructed independent Bernoulli moments as main terms. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Asymptotics Topology

noncomputable def markedProgressionDiscrepancy (H : ℕ → ℝ) (M : ℝ) (Φ : ℝ → ℝ)
    (T x : ℝ) (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R,
    |(∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1), Φ ((u : ℝ) / x) * H u) -
      ((x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) * M|

/-- First-moment progression estimate for the actual divisor weight. -/
theorem marked_actual_first_moment_progressions {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) (he : ∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5)
    (hinj : Function.Injective e) (c A : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (fun x : ℝ => markedProgressionDiscrepancy
      (divisorWeight Finset.univ (fun i => markedLogPowerBand (e i) x)
        (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)))
      (independentArrayMean (fun i => markedLogPowerBand (e i) x)
        (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))) Φ T x ⌊x ^ c⌋₊) =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have h := marked_actual_array_progression_isLittleO e he hinj (fun _ => 1)
    (fun _ => Or.inl rfl) c A hc0 hc1 Φ hT hΦ hderiv hΦT hΦ0
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [marked_array_disjoint_eventually e hinj] with x hd
  unfold markedArrayProgressionDiscrepancy markedProgressionDiscrepancy divisorWeight
  rw [representedArrayEulerMean_one _ (fun i p hp => (mem_markedLogPowerBand.mp hp).1) _ hd]
  simp only [pow_one]

/-- Repeated-array progression estimate, with the genuine second moment
rather than a square of the first moment. -/
theorem marked_actual_second_moment_progressions {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) (he : ∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5)
    (hinj : Function.Injective e) (c A : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (fun x : ℝ => markedProgressionDiscrepancy
      (fun u => (divisorWeight Finset.univ (fun i => markedLogPowerBand (e i) x)
        (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) u) ^ 2)
      (independentArraySecondMoment (fun i => markedLogPowerBand (e i) x)
        (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))) Φ T x ⌊x ^ c⌋₊) =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have h := marked_actual_array_progression_isLittleO e he hinj (fun _ => 2)
    (fun _ => Or.inr rfl) c A hc0 hc1 Φ hT hΦ hderiv hΦT hΦ0
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [marked_array_disjoint_eventually e hinj] with x hd
  unfold markedArrayProgressionDiscrepancy markedProgressionDiscrepancy divisorWeight
  rw [representedArrayEulerMean_two _ (fun i p hp => (mem_markedLogPowerBand.mp hp).1) _ hd]
  simp only [Finset.prod_pow]

end ArtinMatthews
