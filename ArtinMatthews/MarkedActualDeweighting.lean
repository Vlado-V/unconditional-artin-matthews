module

public import ArtinMatthews.MarkedEstimateActualModel
public import ArtinMatthews.MarkedVarianceExpansion
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import ArtinMatthews.MarkedDeweightingBounded
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

/-! Positive prime deweighting for the literal marking arrays. The final
constant is independent of the number of arrays and their particular fixed
exponents; only the threshold for x depends on those choices. -/

namespace ArtinMatthews

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable def markedPrimeSieveFactor (γ : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-Real.eulerMascheroniConstant) / γ * (1 + Real.exp (-(m : ℝ) / 2))

noncomputable def markedPrimeDeweightingConstant (K : ℕ) (γ : ℝ) (m : ℕ)
    (Φ : ℝ → ℝ) (T : ℝ) : ℝ :=
  Real.sqrt (((∫ t in Set.Ioc 0 T, Φ t) * markedPrimeSieveFactor γ m + 1) *
    ((∫ t in Set.Ioc 0 T, Φ t) * markedArrayVarianceConstant K * markedPrimeSieveFactor γ m + 1))

/-- The actual tested prime deweighting error is bounded by a constant
times `b^(-1/2) x/log x`. Every progression and model input is discharged. -/
theorem marked_actual_prime_deweighting {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, (1 / 10 : ℝ) < e j i ∧ e j i < 1 / 5)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2)) (hJ : 0 < Fintype.card J)
    (γ c : ℝ) (m : ℕ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0)
    (F : ℝ → ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᶠ x : ℝ in atTop, ∀ u, (u + 1).Prime → ‖F x u‖ ≤ C) :
    ∀ᶠ x : ℝ in atTop,
      ‖∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime),
        (Φ ((u : ℝ) / x) : ℂ) * F x u *
          ((((∑ j, divisorWeight Finset.univ (fun i => markedLogPowerBand (e j i) x)
            (fun i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u /
              independentArrayMean (fun i => markedLogPowerBand (e j i) x)
                (fun i => bandReciprocalMass (markedLogPowerBand (e j i) x))) /
            Fintype.card J - 1 : ℝ) : ℂ))‖ ≤
        (C * markedPrimeDeweightingConstant (Fintype.card I) γ m Φ T /
          Real.sqrt (Fintype.card J)) * x / Real.log x := by
  classical
  let b : ℝ := Fintype.card J
  let IΦ : ℝ := ∫ t in Set.Ioc 0 T, Φ t
  let D := markedPrimeSieveFactor γ m
  let A₀ := IΦ * D + 1
  let A₁ := IΦ * markedArrayVarianceConstant (Fintype.card I) * D + 1
  have hb : 0 < b := by
    change 0 < (Fintype.card J : ℝ)
    exact_mod_cast hJ
  have hI : 0 ≤ IΦ := integral_nonneg hΦ0
  have hD : 0 ≤ D := by dsimp [D, markedPrimeSieveFactor]; positivity
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := by
    dsimp [A₁]
    have := (markedArrayVarianceConstant_pos (Fintype.card I)).le
    positivity
  have hm₀ := marked_prime_test_mass_upper γ c m hγ hγ1 hc0 hc1 hm hlevel
    Φ hT ha hΦ hderiv hΦT hΦ0 hlow (by norm_num : (0 : ℝ) < 1)
  have hm₁ := marked_actual_prime_variance_upper e he hinj hJ γ c m hγ hγ1 hc0 hc1 hm hlevel
    Φ hT ha hΦ hderiv hΦT hΦ0 hlow (show 0 < 1 / b from one_div_pos.mpr hb)
  filter_upwards [hm₀, hm₁, hF, eventually_gt_atTop (1 : ℝ)] with x hmass hvar hFx hx
  let S := (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime)
  let d (u : ℕ) := ((∑ j, divisorWeight Finset.univ (fun i => markedLogPowerBand (e j i) x)
    (fun i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u /
      independentArrayMean (fun i => markedLogPowerBand (e j i) x)
        (fun i => bandReciprocalMass (markedLogPowerBand (e j i) x))) / Fintype.card J - 1)
  have hmass' : (∑ u ∈ S, Φ ((u : ℝ) / x)) ≤ A₀ * (x / Real.log x) := by
    convert hmass using 1
    dsimp [A₀, IΦ, D, markedPrimeSieveFactor]
    ring
  have hvar' : (∑ u ∈ S, Φ ((u : ℝ) / x) * d u ^ 2) ≤ (A₁ / b) * (x / Real.log x) := by
    convert hvar using 1
    · rfl
    · dsimp [A₁, IΦ, D, markedPrimeSieveFactor, b]
      ring
  have hbound := marked_deweighting_scaled_bounded S (fun u => Φ ((u : ℝ) / x)) d (F x)
    (fun u _ => hΦ0 _) hC (fun u hu => hFx u (Finset.mem_filter.mp hu).2) hA₀ (div_nonneg hA₁ hb.le)
    (div_nonneg (by linarith) (Real.log_pos hx).le) hmass' hvar'
  have heq : C * Real.sqrt (A₀ * (A₁ / b)) * (x / Real.log x) =
      (C * markedPrimeDeweightingConstant (Fintype.card I) γ m Φ T / Real.sqrt (Fintype.card J)) *
        x / Real.log x := by
    rw [show A₀ * (A₁ / b) = (A₀ * A₁) / b by ring,
      Real.sqrt_div (mul_nonneg hA₀ hA₁)]
    change C * (Real.sqrt (A₀ * A₁) / Real.sqrt b) * (x / Real.log x) =
      (C * Real.sqrt (A₀ * A₁) / Real.sqrt b) * x / Real.log x
    ring
  rw [heq] at hbound
  exact hbound

/-- The normalized average whose square is the nonnegative variance weight. -/
noncomputable def markedArrayDeviation {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (P : J → I → Finset ℕ) (V : J → I → ℝ) (u : ℕ) : ℝ :=
  ((∑ j, divisorWeight Finset.univ (P j) (V j) u / independentArrayMean (P j) (V j)) /
    Fintype.card J - 1)

/-- A fixed admissible sieve choice removes all auxiliary sieve parameters.
The constant depends only on the number of bands per array and the test. -/
theorem marked_actual_prime_deweighting_canonical {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (e : J → I → ℝ) (he : ∀ j i, (1 / 10 : ℝ) < e j i ∧ e j i < 1 / 5)
    (hinj : Function.Injective (fun ji : J × I => e ji.1 ji.2)) (hJ : 0 < Fintype.card J)
    (Φ : ℝ → ℝ) {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (hlow : ∀ t < a, Φ t = 0)
    (F : ℝ → ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ᶠ x : ℝ in atTop, ∀ u, (u + 1).Prime → ‖F x u‖ ≤ C) :
    ∀ᶠ x : ℝ in atTop,
      ‖∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => (u + 1).Prime),
        (Φ ((u : ℝ) / x) : ℂ) * F x u *
          (markedArrayDeviation (fun j i => markedLogPowerBand (e j i) x)
            (fun j i => bandReciprocalMass (markedLogPowerBand (e j i) x)) u : ℂ)‖ ≤
        (C * markedPrimeDeweightingConstant (Fintype.card I) (1 / 960048) 20000 Φ T /
          Real.sqrt (Fintype.card J)) * x / Real.log x := by
  exact marked_actual_prime_deweighting e he hinj hJ (1 / 960048) (1 / 2) 20000
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Φ hT ha hΦ hderiv hΦT hΦ0 hlow F hC hF

end ArtinMatthews
