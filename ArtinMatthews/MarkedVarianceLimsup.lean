module

public import ArtinMatthews.MarkedActualDeweighting
public import ArtinMatthews.MarkedLimsupScale
public import ArtinMatthews.MarkedPrimeVariance
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

/-! The exact normalized limsup form of positive prime variance. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable def markedPrimeVarianceSum {J I : Type*}
    [Fintype J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (Φ : ℝ → ℝ) (T x : ℝ) : ℝ :=
  ∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime),
    Φ ((u : ℝ) / x) * markedArrayVarianceWeight
      (fun j i => markedLogPowerBand (e j i) x)
      (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u

/-- Equation (2.9): the actual prime variance has limsup at most an explicit
constant times `C_K/b`, uniformly over fixed distinct band exponents. -/
theorem marked_actual_prime_variance_limsup {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, (1 / 10 : ℝ) < e j i ∧ e j i < 1 / 5)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2)) (hJ : 0 < Fintype.card J)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0) :
    limsup (fun x => Real.log x / x * markedPrimeVarianceSum e Φ T x) atTop ≤
      (∫ t in Set.Ioc 0 T, Φ t) * markedArrayVarianceConstant (Fintype.card I) *
        markedPrimeSieveFactor (1 / 960048) 20000 / Fintype.card J := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply marked_normalized_limsup_le
  · exact Filter.Eventually.of_forall (fun _ =>
      Finset.sum_nonneg (fun _ _ => mul_nonneg (hΦ0 _) (markedArrayVarianceWeight_nonneg _ _ _)))
  · have h := marked_actual_prime_variance_upper e he hinj hJ
      (1 / 960048) (1 / 2) 20000 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      Φ hT ha hΦ hderiv hΦT hΦ0 hlow hε
    filter_upwards [h] with x hx
    convert hx using 1 <;> try rfl
    all_goals
      unfold markedPrimeSieveFactor
      norm_num
      ring

end ArtinMatthews
