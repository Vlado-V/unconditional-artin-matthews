module

public import ArtinMatthews.MarkedEstimateSieveParameters
public import ArtinMatthews.GiantPrimeNormalization
public import ArtinMatthews.GiantRoughSieve
public import ArtinMatthews.GiantActualMoments
public import ArtinMatthews.GiantPrimeInvariance
public import ArtinMatthews.GiantRoughAsymptotic
public import ArtinMatthews.MarkedEstimateActualModel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Actual centered giant-factor rough sums with a constant independent of
the number and locations of the fixed marking bands. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Asymptotics Topology

noncomputable def literalMarkedArrayWeight {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (x : ℝ) (u : ℕ) : ℝ :=
  divisorWeight Finset.univ (fun i => markedLogPowerBand (e i) x)
    (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) u

noncomputable def literalMarkedArrayMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) (x : ℝ) : ℝ :=
  independentArrayMean (fun i => markedLogPowerBand (e i) x)
    (fun i => bandReciprocalMass (markedLogPowerBand (e i) x))

noncomputable def giantCenteredRoughSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (ε : ℝ) (Φ : ℝ → ℝ) (T x γ : ℝ) : ℝ :=
  markedRoughPredecessorSum
    (fun u => ((giantPrimeFactors u x ε).card - giantPrimeReciprocalSum x ε) *
      literalMarkedArrayWeight e x u) Φ T x γ

noncomputable def giantRoughSieveError (Φ : ℝ → ℝ) (T c : ℝ) (m : ℕ) : ℝ :=
  2 * (∫ t in Set.Ioc 0 T, Φ t) * Real.exp (-Real.eulerMascheroniConstant) /
    markedSieveExponent c m * Real.exp (-(m : ℝ) / 2)

theorem literalMarkedArrayWeight_nonneg {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (x : ℝ) (u : ℕ) : 0 ≤ literalMarkedArrayWeight e x u := by
  apply divisorWeight_nonneg
  intro i _
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem literalMarkedArrayMean_lower_eventually {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) :
    ∀ᶠ x : ℝ in atTop, (1 / 2 : ℝ) ^ Fintype.card ι ≤ literalMarkedArrayMean e x :=
  (marked_array_moment_bounds_eventually e he).mono (fun _ hx => hx.1)

/-- The actual rough centered bound (3.8), with constants adapted to the
proved finite block sieve. All giant and ordinary progression inputs are
discharged. Only the threshold in x depends on the fixed array. -/
theorem giant_actual_centered_rough_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) (he : ∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5)
    (hinj : Function.Injective e) (ε c : ℝ) (m : ℕ)
    (hε : 0 < ε) (hεq : ε < 1 / 4) (hc : 0 < c) (hcε : c < ε / 2) (hm : 20000 ≤ m)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t)
    (hΦzero : Φ 0 = 0) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      Real.log x / (x * literalMarkedArrayMean e x) *
          |giantCenteredRoughSum e ε Φ T x (markedSieveExponent c m)| ≤
        giantRoughSieveError Φ T c m + η := by
  have he0 : ∀ i, 0 < e i := fun i => lt_trans (by norm_num) (he i).1
  have hlevel : markedSieveExponent c m * ((12 * (m + 1) : ℕ) : ℝ) ≤ c := by
    calc
      _ = (12 * ((m : ℝ) + 1)) * markedSieveExponent c m := by push_cast; ring
      _ = c / 2 := markedSieveExponent_level c m
      _ ≤ c := by linarith
  have hF : ∀ᶠ x : ℝ in atTop, ∀ u, (0 : ℝ) ≤ (giantPrimeFactors u x ε).card :=
    Filter.Eventually.of_forall (fun _ _ => Nat.cast_nonneg _)
  have hH : ∀ᶠ x : ℝ in atTop, ∀ u, 0 ≤ literalMarkedArrayWeight e x u :=
    Filter.Eventually.of_forall (fun x u => literalMarkedArrayWeight_nonneg e x u)
  have hprogF := giant_actual_first_moment_progressions e he hinj ε c 1
    hε hεq hc.le hcε Φ hT hΦ hderiv hΦT hΦ0 hΦzero
  have hprogH := marked_actual_first_moment_progressions e he hinj c 1 hc.le
    (by linarith : c < 1) Φ hT hΦ hderiv hΦT hΦ0
  exact marked_centered_rough_asymptotic
    (fun x u => ((giantPrimeFactors u x ε).card : ℝ)) (literalMarkedArrayWeight e)
    (fun x => giantPrimeReciprocalSum x ε) (literalMarkedArrayMean e)
    Φ T (markedSieveExponent c m) c m hΦ0 hF hH
    (giantPrimeReciprocalSum_bounds_eventually hε hεq)
    (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ Fintype.card ι)
    (literalMarkedArrayMean_lower_eventually e he0) (markedSieveExponent_pos hc m) hm hlevel
    hprogF hprogH hη

/-- Exact limsup form of the actual rough centered bound, uniform in K
and the fixed band exponents after division by the true array mean. -/
theorem giant_actual_centered_rough_limsup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) (he : ∀ i, (1 / 10 : ℝ) < e i ∧ e i < 1 / 5)
    (hinj : Function.Injective e) (ε c : ℝ) (m : ℕ)
    (hε : 0 < ε) (hεq : ε < 1 / 4) (hc : 0 < c) (hcε : c < ε / 2) (hm : 20000 ≤ m)
    (Φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t)
    (hΦzero : Φ 0 = 0) :
    limsup (fun x : ℝ => Real.log x / (x * literalMarkedArrayMean e x) *
      |giantCenteredRoughSum e ε Φ T x (markedSieveExponent c m)|) atTop ≤
        giantRoughSieveError Φ T c m := by
  have hn : ∀ᶠ x : ℝ in atTop,
      0 ≤ Real.log x / (x * literalMarkedArrayMean e x) *
        |giantCenteredRoughSum e ε Φ T x (markedSieveExponent c m)| := by
    filter_upwards [literalMarkedArrayMean_lower_eventually e
      (fun i => lt_trans (by norm_num) (he i).1), eventually_gt_atTop (1 : ℝ)] with x hM hx
    have hm0 : 0 < literalMarkedArrayMean e x := lt_of_lt_of_le (by positivity) hM
    exact mul_nonneg (div_nonneg (Real.log_pos hx).le (mul_nonneg (by linarith) hm0.le))
      (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro η hη
  exact limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop hn)
    (giant_actual_centered_rough_bound e he hinj ε c m hε hεq hc hcε hm
      Φ hT hΦ hderiv hΦT hΦ0 hΦzero hη)

/-- The remaining sieve-depth error vanishes after all fixed-array x limits. -/
theorem giantRoughSieveError_tendsto (Φ : ℝ → ℝ) (T c : ℝ) :
    Tendsto (giantRoughSieveError Φ T c) atTop (𝓝 0) := by
  have h := (markedSieve_error_tendsto c).const_mul
    (2 * (∫ t in Set.Ioc 0 T, Φ t) * Real.exp (-Real.eulerMascheroniConstant))
  convert h using 1
  · ext m
    unfold giantRoughSieveError
    ring
  · ring

end ArtinMatthews
