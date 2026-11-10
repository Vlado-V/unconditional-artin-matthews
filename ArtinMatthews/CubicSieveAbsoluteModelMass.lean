module

public import ArtinMatthews.CubicSieveProgressionEuler
public import ArtinMatthews.MarkedMajorArcRoughMertens
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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute coefficient masses used only for the negligible marking
comparison errors. The signed main model remains unchanged. -/

noncomputable section
namespace ArtinMatthews

open Finset Filter
open scoped BigOperators Topology

def cubicSieveCorrectionAbsoluteMass (z : ℝ) (m : ℕ) : ℝ :=
  ∑ R ∈ (Nat.primesLE ⌊z⌋₊).powerset, |cubicSieveCorrectionCoeff z m R| *
    cubicSieveDivisorFactor (roughSubsetDivisor R) 1

def cubicSieveCorrectionDerivativeMass (z : ℝ) (m : ℕ) : ℝ :=
  ∑ R ∈ (Nat.primesLE ⌊z⌋₊).powerset, |cubicSieveCorrectionCoeff z m R| *
    |cubicSieveDivisorLogMoment (roughSubsetDivisor R)|

theorem cubicSieve_divisorFactor_one_nonneg {r : ℕ} (hr : Squarefree r) :
    0 ≤ cubicSieveDivisorFactor r 1 := by
  rw [cubicSieve_divisorFactor_eq_prod hr]
  apply prod_nonneg
  intro p hp
  rw [cubicSieve_primeDivisorModel_one (Nat.prime_of_mem_primeFactors hp).pos]
  exact (cubicSieve_primeDivisorDensity_bounds (Nat.prime_of_mem_primeFactors hp)).1

theorem cubicSieve_divisorLogMoment_abs_le {r : ℕ} (hr : Squarefree r) :
    |cubicSieveDivisorLogMoment r| ≤ Real.log (r : ℝ) * cubicSieveDivisorFactor r 1 := by
  have hP (p : ℕ) (hp : p ∈ r.primeFactors) := Nat.prime_of_mem_primeFactors hp
  have h := cubicSieve_hasDerivAt_prod r.primeFactors
    (fun p s => cubicSievePrimeDivisorModel s p) cubicSievePrimeDivisorDensityDerivative 1
    (fun p hp => cubicSieve_primeDivisorModel_hasDerivAt_one (hP p hp).pos)
  have heq : cubicSieveDivisorFactor r = fun s => ∏ p ∈ r.primeFactors, cubicSievePrimeDivisorModel s p :=
    funext (fun s => cubicSieve_divisorFactor_eq_prod hr s)
  have hd := (cubicSieve_divisorFactor_hasDerivAt_one (Nat.pos_of_ne_zero hr.ne_zero)).deriv
  rw [heq, h.deriv] at hd
  have hg (p : ℕ) (hp : p ∈ r.primeFactors) : 0 ≤ cubicSievePrimeDivisorModel 1 p := by
    rw [cubicSieve_primeDivisorModel_one (hP p hp).pos]
    exact (cubicSieve_primeDivisorDensity_bounds (hP p hp)).1
  have hv (p : ℕ) (hp : p ∈ r.primeFactors) :
      |cubicSievePrimeDivisorDensityDerivative p| ≤ Real.log (p : ℝ) * cubicSievePrimeDivisorModel 1 p := by
    rw [cubicSieve_primeDivisorModel_one (hP p hp).pos]
    exact cubicSieve_primeDivisorDensityDerivative_abs_le (hP p hp)
  have hs : (∑ p ∈ r.primeFactors, Real.log (p : ℝ)) = Real.log (r : ℝ) := by
    rw [← Real.log_prod (s := r.primeFactors) (f := fun p : ℕ => (p : ℝ))
      (fun p hp => Nat.cast_ne_zero.mpr (hP p hp).ne_zero),
      ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  have hb := cubicSieve_prodTangent_abs_le r.primeFactors
    (fun p => cubicSievePrimeDivisorModel 1 p) cubicSievePrimeDivisorDensityDerivative
    (fun p => Real.log (p : ℝ)) hg hv
  rw [hd, abs_neg, hs] at hb
  rw [cubicSieve_divisorFactor_eq_prod hr]
  exact hb

theorem cubicSieve_correctionAbsoluteMass_le (z : ℝ) (m : ℕ) :
    cubicSieveCorrectionAbsoluteMass z m ≤ (markedSieveEulerProduct z)⁻¹ ^ 2 := by
  let P := Nat.primesLE ⌊z⌋₊
  have hp (p : ℕ) (hp : p ∈ P) := Nat.prime_of_mem_primesLE hp
  have hfac (R : Finset ℕ) (hR : R ∈ P.powerset) :
      cubicSieveDivisorFactor (roughSubsetDivisor R) 1 = ∏ p ∈ R, cubicSievePrimeDivisorDensity p := by
    rw [cubicSieve_divisorFactor_eq_prod (roughSubsetDivisor_squarefree R
      (fun p hp' => hp p (mem_powerset.mp hR hp')))]
    unfold roughSubsetDivisor
    rw [Nat.primeFactors_prod (fun p hp' => hp p (mem_powerset.mp hR hp'))]
    apply prod_congr rfl
    intro p hp'
    exact cubicSieve_primeDivisorModel_one (hp p (mem_powerset.mp hR hp')).pos
  unfold cubicSieveCorrectionAbsoluteMass
  calc
    _ ≤ ∑ R ∈ P.powerset, ∏ p ∈ R, cubicSievePrimeDivisorDensity p := by
      apply sum_le_sum
      intro R hR
      rw [hfac R hR]
      exact mul_le_of_le_one_left
        (prod_nonneg (fun p hp' => (cubicSieve_primeDivisorDensity_bounds (hp p (mem_powerset.mp hR hp'))).1))
        (cubicSieve_correctionCoeff_abs_le z m R)
    _ = ∏ p ∈ P, (1 + cubicSievePrimeDivisorDensity p) := (prod_one_add P).symm
    _ ≤ (∏ p ∈ P, (1 + (p : ℝ)⁻¹)) ^ 2 := by
      rw [← prod_pow]
      apply prod_le_prod₀
      · intro p hp'
        exact add_nonneg zero_le_one (cubicSieve_primeDivisorDensity_bounds (hp p hp')).1
      · intro p hp'
        unfold cubicSievePrimeDivisorDensity
        nlinarith only [sq_nonneg (p : ℝ)⁻¹]
    _ ≤ _ := pow_le_pow_left₀
      (prod_nonneg (fun p _ => by positivity)) (marked_rough_plus_product_le_inverse z) 2

theorem cubicSieve_correctionDerivativeMass_le {z : ℝ} (hz : 1 < z) (m : ℕ) :
    cubicSieveCorrectionDerivativeMass z m ≤
      (8 * (m : ℝ) + 2) * Real.log z * cubicSieveCorrectionAbsoluteMass z m := by
  unfold cubicSieveCorrectionDerivativeMass cubicSieveCorrectionAbsoluteMass
  rw [mul_sum]
  apply sum_le_sum
  intro R hR
  by_cases hzero : cubicSieveCorrectionCoeff z m R = 0
  · simp only [hzero, abs_zero, zero_mul, mul_zero, le_refl]
  have hP (p : ℕ) (hp : p ∈ R) := Nat.prime_of_mem_primesLE (mem_powerset.mp hR hp)
  have hsq := roughSubsetDivisor_squarefree R hP
  have hpos := roughSubsetDivisor_pos R hP
  have hlevel := (cubicSieve_correctionCoeff_level hz (mem_powerset.mp hR) hzero).2.2
  have hlog := Real.log_le_log (by exact_mod_cast hpos : (0 : ℝ) < roughSubsetDivisor R) hlevel
  rw [Real.log_rpow (zero_lt_one.trans hz)] at hlog
  have hb := cubicSieve_divisorLogMoment_abs_le hsq
  have hnonneg := cubicSieve_divisorFactor_one_nonneg hsq
  exact (mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right hlog hnonneg))
    (abs_nonneg _)).trans_eq (by ring)

end ArtinMatthews
