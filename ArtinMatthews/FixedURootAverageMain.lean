module

public import ArtinMatthews.FixedURootAverage
public import ArtinMatthews.FixedURootEuler
public import ArtinMatthews.FixedURootTail
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

/-! The complete Euler main term for the progression average of the actual
fixed-u root density, with uniform logarithmic remainder. -/
namespace ArtinMatthews
open OAI.Erdos970 ErdosHyperbolaError
open scoped BigOperators ArithmeticFunction.Moebius

/-- The progression average with the true infinite Euler coefficient. -/
theorem fixedURootDensity_progression_average_infinite (N S : ℕ)
    (hN : 0 < N) (hS : 0 < S) (a : ℤ)
    (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N) (lc rc : Bool) :
    |(∑ n ∈ (realIntervalIntegers x y lc rc).filter
        (fun n => Int.ModEq (S : ℤ) n a),
        fixedURootDensity n.natAbs (Nat.gcd S n.natAbs)) -
      (y-x)/(S : ℝ) * (∑' d, fixedURootEulerTerm S d)| ≤
      1+Real.log N + (y-x)/((S : ℝ)*(N : ℝ)) := by
  have havg := fixedURootDensity_progression_average N S hS a x y hx hxy hyN lc rc
  have he : (∑ d ∈ fixedURootDivisors N S, (μ d : ℝ)/(d : ℝ)^2) =
      ∑ d ∈ Finset.Icc 1 N, fixedURootEulerTerm S d := by
    simp only [fixedURootDivisors,Finset.sum_filter,fixedURootEulerTerm]
  rw [he] at havg
  have htail := fixedURootEuler_truncation_error S N hN
  rw [abs_sub_comm] at htail
  have hfactor : 0 ≤ (y-x)/(S : ℝ) :=
    div_nonneg (sub_nonneg.mpr hxy) (Nat.cast_nonneg S)
  calc
    _ = |((∑ n ∈ (realIntervalIntegers x y lc rc).filter
        (fun n => Int.ModEq (S : ℤ) n a),
        fixedURootDensity n.natAbs (Nat.gcd S n.natAbs)) -
        (y-x)/(S : ℝ) * ∑ d ∈ Finset.Icc 1 N, fixedURootEulerTerm S d) +
        (y-x)/(S : ℝ) * ((∑ d ∈ Finset.Icc 1 N, fixedURootEulerTerm S d) -
          ∑' d, fixedURootEulerTerm S d)| := by congr 1; ring
    _ ≤ |(∑ n ∈ (realIntervalIntegers x y lc rc).filter
        (fun n => Int.ModEq (S : ℤ) n a),
        fixedURootDensity n.natAbs (Nat.gcd S n.natAbs)) -
        (y-x)/(S : ℝ) * ∑ d ∈ Finset.Icc 1 N, fixedURootEulerTerm S d| +
        |(y-x)/(S : ℝ) * ((∑ d ∈ Finset.Icc 1 N, fixedURootEulerTerm S d) -
          ∑' d, fixedURootEulerTerm S d)| := abs_add_le _ _
    _ ≤ 1+Real.log N + ((y-x)/(S : ℝ)) * (1/(N : ℝ)) := by
      apply add_le_add havg
      rw [abs_mul,abs_of_nonneg hfactor]
      exact mul_le_mul_of_nonneg_left htail hfactor
    _ = _ := by ring

/-- The actual progression Euler main term, with error `2+log N` uniform in
the modulus, residue and interval endpoints. -/
theorem fixedURootDensity_progression_average_zeta (N S : ℕ)
    (hN : 0 < N) (hS : 0 < S) (a : ℤ)
    (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyN : y ≤ N) (lc rc : Bool) :
    |(∑ n ∈ (realIntervalIntegers x y lc rc).filter
        (fun n => Int.ModEq (S : ℤ) n a),
        fixedURootDensity n.natAbs (Nat.gcd S n.natAbs)) -
      (y-x)/(S : ℝ) * ((riemannZeta 2).re)⁻¹ *
        (∏ p ∈ S.primeFactors, (1-1/(p : ℝ)^2)⁻¹)| ≤ 2+Real.log N := by
  let : NeZero S := ⟨hS.ne'⟩
  have hh := fixedURootDensity_progression_average_infinite N S hN hS a x y hx hxy hyN lc rc
  rw [fixedURootEuler_sum_zeta] at hh
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < (S : ℝ)*(N : ℝ) := by positivity
  have hlen : y-x ≤ (S : ℝ)*(N : ℝ) := by nlinarith
  have herr : (y-x)/((S : ℝ)*(N : ℝ)) ≤ 1 := (div_le_one hden).mpr hlen
  convert hh.trans (show 1+Real.log N+(y-x)/((S : ℝ)*(N : ℝ)) ≤ 2+Real.log N by linarith) using 1
  congr 2
  ring

end ArtinMatthews
