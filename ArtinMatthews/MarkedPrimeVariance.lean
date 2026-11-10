module

public import ArtinMatthews.MarkedEstimateActualModel
public import ArtinMatthews.MarkedVarianceExpansion
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import ArtinMatthews.MarkedActualVarianceProgressions
public import ArtinMatthews.MarkedProgressionLinear
public import ArtinMatthews.MarkedSieveAsymptotic
public import ArtinMatthews.MarkedSieveSupport
public import ArtinMatthews.MarkedVarianceModelBounds
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Prime variance bound for the actual marking arrays. Both the arithmetic
progression estimate and the independent-model variance bound have been
proved; the small-prime cutoff disappears by the test's support. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Topology

theorem marked_actual_prime_variance_upper {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, (1 / 10 : ℝ) < e j i ∧ e j i < 1 / 5)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2)) (hJ : 0 < Fintype.card J)
    (γ c : ℝ) (m : ℕ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime),
        Φ ((u : ℝ) / x) * markedArrayVarianceWeight
          (fun j i => markedLogPowerBand (e j i) x)
          (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u) ≤
        (((∫ t in Set.Ioc 0 T, Φ t) *
            (markedArrayVarianceConstant (Fintype.card I) / Fintype.card J) *
            Real.exp (-Real.eulerMascheroniConstant) / γ * (1 + Real.exp (-(m : ℝ) / 2)) + ε) *
          x / Real.log x) := by
  let H (x : ℝ) := markedArrayVarianceWeight (fun j i => markedLogPowerBand (e j i) x)
    (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x))
  let M (x : ℝ) := independentArraysVariance (fun j i => markedLogPowerBand (e j i) x)
    (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x))
  have hH : ∀ᶠ x : ℝ in atTop, ∀ u, 0 ≤ H x u :=
    Filter.Eventually.of_forall (fun _ _ => markedArrayVarianceWeight_nonneg _ _ _)
  have hM : ∀ᶠ x : ℝ in atTop, 0 ≤ M x ∧
      M x ≤ markedArrayVarianceConstant (Fintype.card I) / Fintype.card J :=
    marked_actual_variance_model_bounds e (fun j i => lt_trans (by norm_num) (he j i).1) hinj hJ
  have hprog := marked_actual_variance_progressions e he hinj hJ c 1 hc0 hc1
    Φ hT hΦ hderiv hΦT hΦ0
  have h := marked_sieve_asymptotic H M Φ T γ c
    (markedArrayVarianceConstant (Fintype.card I) / Fintype.card J) m
    hΦ0 hH hM hγ hm hlevel hprog hε
  filter_upwards [h, marked_prime_cutoff_eq_eventually (fun x => Finset.Icc 0 ⌊T * x⌋₊)
    H Φ ha hγ1 hlow] with x hx heq
  rw [heq] at hx
  exact hx

/-- The same arithmetic sieve gives an upper bound for the unmarked
smooth prime mass, required by the Cauchy step. -/
theorem marked_prime_test_mass_upper (γ c : ℝ) (m : ℕ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime), Φ ((u : ℝ) / x)) ≤
        (((∫ t in Set.Ioc 0 T, Φ t) * Real.exp (-Real.eulerMascheroniConstant) / γ *
            (1 + Real.exp (-(m : ℝ) / 2)) + ε) * x / Real.log x) := by
  have hprog := markedProgressionDiscrepancy_one_all_log c 1 hc0 hc1 Φ hT hΦ hderiv hΦT hΦ0
  have h := marked_sieve_asymptotic (fun _ _ => 1) (fun _ => 1) Φ T γ c 1 m hΦ0
    (Filter.Eventually.of_forall (fun _ _ => by norm_num))
    (Filter.Eventually.of_forall (fun _ => by norm_num)) hγ hm hlevel hprog hε
  filter_upwards [h, marked_prime_cutoff_eq_eventually (fun x => Finset.Icc 0 ⌊T * x⌋₊)
    (fun _ _ => 1) Φ ha hγ1 hlow] with x hx heq
  rw [heq] at hx
  simpa only [mul_one] using hx

end ArtinMatthews
