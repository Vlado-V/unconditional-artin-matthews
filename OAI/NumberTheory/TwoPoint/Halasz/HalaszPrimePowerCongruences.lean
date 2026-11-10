module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowerRoots
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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
public import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowerSums


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Triangular systems of univariate polynomials reduce to power sums.
The leading coefficients need only be units, so the result applies to
the translated and differenced systems over prime-power residue rings. -/
namespace TwoPointCorrelations

open Finset Polynomial

theorem halasz_power_sums_of_polynomial_sums {R : Type*} [CommRing R] {k : ℕ}
    (P : Fin k → R[X]) (x y : Fin k → R)
    (hdeg : ∀ i, (P i).natDegree ≤ i.val+1)
    (hunit : ∀ i, IsUnit ((P i).coeff (i.val+1)))
    (hsum : ∀ i, ∑ j, (P i).eval (x j)=∑ j, (P i).eval (y j)) :
    ∀ j : ℕ, 1≤j → j≤k → ∑ i, x i^j=∑ i, y i^j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj hjk
    let l : Fin k := ⟨j-1,by omega⟩
    let Q := P l
    have hd : Q.natDegree < j+1 := by
      exact Nat.lt_succ_of_le (by
        simpa only [Q,l,Nat.sub_add_cancel hj] using hdeg l)
    have heval (z : Fin k → R) :
        (∑ i, Q.eval (z i)) = ∑ m ∈ range (j+1), Q.coeff m*(∑ i, z i^m) := by
      simp_rw [Polynomial.eval_eq_sum_range' hd]
      rw [sum_comm]
      simp_rw [← mul_sum]
    have hs := hsum l
    change (∑ i, Q.eval (x i)) = ∑ i, Q.eval (y i) at hs
    rw [heval,heval,sum_range_succ,sum_range_succ] at hs
    have hsmall : (∑ m ∈ range j, Q.coeff m*(∑ i, x i^m)) =
        ∑ m ∈ range j, Q.coeff m*(∑ i, y i^m) := by
      apply sum_congr rfl
      intro m hm
      have hmj := mem_range.mp hm
      by_cases hm0 : m=0
      · simp [hm0]
      · rw [ih m hmj (by omega) (by omega)]
    rw [hsmall] at hs
    have hu : IsUnit (Q.coeff j) := by
      simpa only [Q,l,Nat.sub_add_cancel hj] using hunit l
    exact hu.mul_right_inj.mp (add_left_cancel hs)

theorem halasz_prime_power_polynomial_count {p r k : ℕ} [Fact p.Prime]
    (hkp : k<p) (P : Fin k → (ZMod (p^(r+1)))[X])
    (hdeg : ∀ i, (P i).natDegree ≤ i.val+1)
    (hunit : ∀ i, IsUnit ((P i).coeff (i.val+1)))
    (x : Fin k → ZMod (p^(r+1)))
    (hx : Function.Injective (fun i => halaszPrimePowerReduction p r (x i)))
    (F : Finset (Fin k → ZMod (p^(r+1))))
    (hF : ∀ y∈F, ∀ i, ∑ j, (P i).eval (x j)=∑ j, (P i).eval (y j)) :
    F.card ≤ k^k := by
  apply halasz_prime_power_solution_count hkp x hx F
  intro y hy
  exact halasz_power_sums_of_polynomial_sums P x y hdeg hunit (hF y hy)

end TwoPointCorrelations

end OAI
