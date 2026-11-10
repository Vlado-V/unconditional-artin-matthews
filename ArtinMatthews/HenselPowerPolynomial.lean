module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Basify


set_option backward.privateInPublic true
@[expose] public section

/-! A monic polynomial realizing the strong Hensel power-unit construction.
Its reduction is X^d-X^(d-1), with a simple root at one. -/
noncomputable section
namespace ArtinMatthews.HenselPower
open Polynomial Finset
open scoped BigOperators
variable {R : Type*} [CommRing R]

/-- Lower-degree correction in the strong Hensel binomial polynomial. -/
def powerTail (d : ℕ) (t : R) : R[X] :=
  ∑ k ∈ range (d - 1), C ((d.choose (k + 2) : R) * (d : R)^k * t^(k+1)) * X^(d-(k+2))

def powerPolynomial (d : ℕ) (t : R) : R[X] := X^d - (X^(d-1) + powerTail d t)

theorem powerTail_natDegree_lt (d : ℕ) (hd : 0 < d) (t : R) :
    (powerTail d t).natDegree < d := by
  unfold powerTail
  apply (natDegree_sum_le_of_forall_le (n := d-1) _ _ ?_).trans_lt
    (Nat.sub_lt hd (by omega : 0 < 1))
  intro k hk
  apply (natDegree_C_mul_X_pow_le _ _).trans
  omega

theorem powerPolynomial_monic [Nontrivial R] (d : ℕ) (hd : 0 < d) (t : R) :
    (powerPolynomial d t).Monic := by
  apply (isMonicOfDegree_X_pow R d).sub _ |>.monic
  apply (natDegree_add_le _ _).trans_lt
  exact max_lt (by simpa using Nat.sub_lt hd (by omega : 0 < 1))
    (powerTail_natDegree_lt d hd t)

theorem powerTail_eval (d : ℕ) (t w : R) :
    (powerTail d t).eval w =
      ∑ k ∈ range (d - 1), (d.choose (k + 2) : R) * (d : R)^k * t^(k+1) * w^(d-(k+2)) := by
  simp only [powerTail, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

/-- The binomial identity behind the strong Hensel construction. -/
theorem binomial_power_identity (d : ℕ) (hd : 0 < d) (t w : R) :
    (w + (d : R) * t)^d = w^d + (d : R)^2 * t *
      (w^(d-1) + (powerTail d t).eval w) := by
  rw [add_comm w, add_pow, powerTail_eval]
  have hn : d + 1 = 2 + (d - 1) := by omega
  rw [hn, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
    Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.choose_one_right, pow_one]
  rw [mul_add, Finset.mul_sum, ← add_assoc]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [Nat.add_comm 2, mul_pow, pow_add]
    ring

/-- A unit root of the monic auxiliary polynomial gives the desired power identity. -/
theorem power_eq_of_isRoot (d : ℕ) (hd : 0 < d) (t : R) (w : Rˣ)
    (hw : (powerPolynomial d t).IsRoot (w : R)) :
    ((w : R) + (d : R) * t)^d = (1 + (d : R)^2 * t) * (w : R)^d := by
  have hw' : (w : R)^d = (w : R)^(d-1) + (powerTail d t).eval (w : R) := by
    simpa only [IsRoot, powerPolynomial, eval_sub, eval_add, eval_pow, eval_X,
      sub_eq_zero] using hw
  rw [binomial_power_identity d hd, ← hw']
  ring

end ArtinMatthews.HenselPower
