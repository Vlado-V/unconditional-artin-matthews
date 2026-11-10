module

public import ArtinMatthews.CubicSieveDivisorConvolution
public import ArtinMatthews.CubicSieveCorrectionModel
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact exponential Euler monomials and the source divisor factor. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveEulerPower (n : ℕ) (s : ℝ) : ℝ :=
  Real.exp (-(s * Real.log (n : ℝ)))

theorem cubicSieve_eulerPower_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (s : ℝ) :
    cubicSieveEulerPower (a * b) s = cubicSieveEulerPower a s * cubicSieveEulerPower b s := by
  unfold cubicSieveEulerPower
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity), mul_add, neg_add, Real.exp_add]

theorem cubicSieve_eulerPower_prod (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (s : ℝ) :
    cubicSieveEulerPower (roughSubsetDivisor P) s = ∏ p ∈ P, cubicSieveEulerPower p s := by
  unfold cubicSieveEulerPower roughSubsetDivisor
  rw [Nat.cast_prod, Real.log_prod (s := P) (f := fun p : ℕ => (p : ℝ))
    (fun p hp => Nat.cast_ne_zero.mpr (hP p hp).ne'),
    mul_sum, ← sum_neg_distrib, Real.exp_sum]

theorem cubicSieve_eulerPower_one {n : ℕ} (hn : 0 < n) :
    cubicSieveEulerPower n 1 = (n : ℝ)⁻¹ := by
  simp only [cubicSieveEulerPower, one_mul, Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < n)]

theorem cubicSieve_eulerPower_hasDerivAt (n : ℕ) (s : ℝ) :
    HasDerivAt (cubicSieveEulerPower n)
      (-Real.log (n : ℝ) * cubicSieveEulerPower n s) s := by
  have h := (((hasDerivAt_id s).mul_const (Real.log (n : ℝ))).neg.exp)
  convert h using 1
  · funext t
    simp only [cubicSieveEulerPower, Pi.neg_apply, id_eq]
  · simp only [cubicSieveEulerPower, Pi.neg_apply, id_eq, one_mul]
    ring

theorem cubicSieve_divisorEulerCoeff_eval (P : Finset ℕ) (w : ℕ → ℝ) :
    (∑ T ∈ P.powerset, cubicSieveDivisorEulerCoeff P T * ∏ p ∈ T, w p) =
      ∏ p ∈ P, (2 - w p) := by
  calc
    _ = ∑ T ∈ P.powerset, (∏ p ∈ T, -w p) * ∏ _p ∈ P \ T, (2 : ℝ) := by
      apply sum_congr rfl
      intro T hT
      rw [cubicSieveDivisorEulerCoeff, prod_ite, filter_mem_eq_inter,
        inter_eq_right.mpr (mem_powerset.mp hT), filter_notMem_eq_sdiff]
      calc
        _ = ((∏ _p ∈ T, (-1 : ℝ)) * ∏ p ∈ T, w p) * ∏ _p ∈ P \ T, (2 : ℝ) := by ring
        _ = _ := by rw [← prod_mul_distrib]; simp only [neg_one_mul]
    _ = ∏ p ∈ P, (-w p + 2) := (prod_add _ _ _).symm
    _ = _ := by apply prod_congr rfl; intro p _; ring

def cubicSieveDivisorFactor (r : ℕ) (s : ℝ) : ℝ :=
  ∑ T ∈ r.primeFactors.powerset, cubicSieveDivisorEulerCoeff r.primeFactors T *
    cubicSieveEulerPower (r * roughSubsetDivisor T) s

theorem cubicSieve_divisorFactor_eq_prod {r : ℕ} (hr : Squarefree r) (s : ℝ) :
    cubicSieveDivisorFactor r s = ∏ p ∈ r.primeFactors, cubicSievePrimeDivisorModel s p := by
  have hr₀ := Nat.pos_of_ne_zero hr.ne_zero
  have hP (p : ℕ) (hp : p ∈ r.primeFactors) : 0 < p :=
    (Nat.prime_of_mem_primeFactors hp).pos
  have hprod : roughSubsetDivisor r.primeFactors = r := Nat.prod_primeFactors_of_squarefree hr
  calc
    _ = cubicSieveEulerPower r s *
        ∑ T ∈ r.primeFactors.powerset, cubicSieveDivisorEulerCoeff r.primeFactors T *
          ∏ p ∈ T, cubicSieveEulerPower p s := by
      rw [mul_sum]
      apply sum_congr rfl
      intro T hT
      rw [cubicSieve_eulerPower_mul hr₀
        (roughSubsetDivisor_pos T (fun p hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp))),
        cubicSieve_eulerPower_prod T (fun p hp => hP p (mem_powerset.mp hT hp))]
      ring
    _ = (∏ p ∈ r.primeFactors, cubicSieveEulerPower p s) *
        ∏ p ∈ r.primeFactors, (2 - cubicSieveEulerPower p s) := by
      rw [cubicSieve_divisorEulerCoeff_eval, ← cubicSieve_eulerPower_prod _ hP, hprod]
    _ = _ := by
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro p _
      unfold cubicSievePrimeDivisorModel cubicSieveEulerPower
      ring

end ArtinMatthews
