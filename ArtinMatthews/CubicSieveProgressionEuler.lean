module

public import ArtinMatthews.CubicSieveMarkingEuler
public import ArtinMatthews.CubicSieveDivisorLogProgression
public import ArtinMatthews.CubicSieveDivisorModelNormalized
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

/-! The arithmetic logarithmic density is the value and derivative of
the same Euler factors appearing in the signed sieve model. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveDivisorLeading (r : ℕ) : ℝ :=
  ∑ T ∈ r.primeFactors.powerset, cubicSieveDivisorEulerCoeff r.primeFactors T /
    ((r * roughSubsetDivisor T : ℕ) : ℝ)

def cubicSieveDivisorLogMoment (r : ℕ) : ℝ :=
  ∑ T ∈ r.primeFactors.powerset, cubicSieveDivisorEulerCoeff r.primeFactors T *
    Real.log ((r * roughSubsetDivisor T : ℕ) : ℝ) / ((r * roughSubsetDivisor T : ℕ) : ℝ)

theorem cubicSieve_divisorFactor_one {r : ℕ} (hr : 0 < r) :
    cubicSieveDivisorFactor r 1 = cubicSieveDivisorLeading r := by
  unfold cubicSieveDivisorFactor cubicSieveDivisorLeading
  apply sum_congr rfl
  intro T hT
  rw [cubicSieve_eulerPower_one (Nat.mul_pos hr
    (roughSubsetDivisor_pos T (fun p hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp))))]
  rfl

theorem cubicSieve_divisorFactor_hasDerivAt_one {r : ℕ} (hr : 0 < r) :
    HasDerivAt (cubicSieveDivisorFactor r) (-cubicSieveDivisorLogMoment r) 1 := by
  have h := HasDerivAt.fun_sum (u := r.primeFactors.powerset) (fun T _ =>
    (cubicSieve_eulerPower_hasDerivAt (r * roughSubsetDivisor T) 1).const_mul
      (cubicSieveDivisorEulerCoeff r.primeFactors T))
  convert h using 1
  · rfl
  · rw [cubicSieveDivisorLogMoment, ← sum_neg_distrib]
    apply sum_congr rfl
    intro T hT
    rw [cubicSieve_eulerPower_one (Nat.mul_pos hr
      (roughSubsetDivisor_pos T (fun p hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp))))]
    ring

def cubicSieveProgressionEulerFactor (d r : ℕ) (s : ℝ) : ℝ :=
  cubicSieveDivisorFactor r s * cubicSieveMarkingFactor d s

theorem cubicSieve_progressionEulerFactor_deriv_one {d r : ℕ} (hd : 0 < d) (hr : 0 < r) :
    deriv (cubicSieveProgressionEulerFactor d r) 1 =
      -cubicSieveDivisorLogMoment r * (cubicSieveCoprimeDensity d / (d : ℝ)) +
        cubicSieveDivisorLeading r * (-2 * cubicSieveCoprimeLogMoment d / (d : ℝ)) := by
  have h := (cubicSieve_divisorFactor_hasDerivAt_one hr).mul (cubicSieve_markingFactor_hasDerivAt_one hd)
  rw [cubicSieve_markingFactor_one hd, cubicSieve_divisorFactor_one hr] at h
  exact h.deriv

theorem cubicSieve_shiftedDivisorLogDensity_eq_factors {d r : ℕ}
    (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    cubicSieveShiftedDivisorLogDensity d r t =
      ((Real.log t + 2 * Real.eulerMascheroniConstant) * cubicSieveCoprimeDensity d -
        2 * cubicSieveCoprimeLogMoment d) / (d : ℝ) * cubicSieveDivisorLeading r -
      (cubicSieveCoprimeDensity d / (d : ℝ)) * cubicSieveDivisorLogMoment r := by
  unfold cubicSieveShiftedDivisorLogDensity cubicSieveDivisorLeading cubicSieveDivisorLogMoment
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro T hT
  have ha : (0 : ℝ) < ((r * roughSubsetDivisor T : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hr (roughSubsetDivisor_pos T
      (fun p hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp)))
  unfold cubicSieveDivisorUnitDensity
  rw [Real.log_div ht.ne' ha.ne']
  ring

theorem cubicSieve_shiftedDivisorLogDensity_eq_value_derivative {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) {t : ℝ} (ht : 0 < t) :
    cubicSieveShiftedDivisorLogDensity d r t =
      (Real.log t + 2 * Real.eulerMascheroniConstant) * cubicSieveProgressionEulerFactor d r 1 +
        deriv (cubicSieveProgressionEulerFactor d r) 1 := by
  rw [cubicSieve_shiftedDivisorLogDensity_eq_factors hr ht,
    cubicSieve_progressionEulerFactor_deriv_one hd hr,
    cubicSieveProgressionEulerFactor, cubicSieve_divisorFactor_one hr, cubicSieve_markingFactor_one hd]
  ring

theorem cubicSieve_correctionModel_eq_divisorFactor (z : ℝ) (m : ℕ) (s : ℝ) :
    cubicSieveDivisorCorrectionModel z m s =
      ∑ R ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m R *
        cubicSieveDivisorFactor (roughSubsetDivisor R) s := by
  unfold cubicSieveDivisorCorrectionModel cubicSieveCorrectionModel
  apply sum_congr rfl
  intro R hR
  have hP (p : ℕ) (hp : p ∈ R) : p.Prime := Nat.prime_of_mem_primesLE (mem_powerset.mp hR hp)
  rw [cubicSieve_divisorFactor_eq_prod (roughSubsetDivisor_squarefree R hP)]
  unfold roughSubsetDivisor
  rw [Nat.primeFactors_prod hP]

end ArtinMatthews
