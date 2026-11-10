module

public import ArtinMatthews.RoughBonferroniDivisors
public import OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity
public import ArtinMatthews.RoughBonferroniLayerBounds
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual reciprocal-divisor truncation approximates its Euler product
with the next elementary layer as its explicit error. -/
noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators Classical
open OAI.Erdos970.NumberTheoryLean.BonferroniDensity

/-- The literal rough-number Euler density. -/
def roughCharacterEulerDensity (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - 1 / (p : ℝ))

/-- The signed reciprocal-divisor main term of the finite truncation. -/
def roughCharacterDensityTruncation (P : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ S ∈ roughTruncationSubsets P r, (-1 : ℝ) ^ S.card / (roughSubsetDivisor S : ℝ)

theorem roughCharacterDensityTruncation_eq (P : Finset ℕ) (r : ℕ) :
    roughCharacterDensityTruncation P r = densityPolynomial r P (fun p => 1 / (p : ℝ)) := by
  unfold roughCharacterDensityTruncation densityPolynomial
  rw [sum_roughTruncationSubsets]
  apply sum_congr rfl
  intro j _
  rw [← rough_layer_reciprocal_mass_eq, mul_sum]
  apply sum_congr rfl
  intro S hS
  rw [(mem_powersetCard.mp hS).2]
  ring

/-- Every truncation order has Euler-density error at most the next layer. -/
theorem roughCharacterDensityTruncation_error_le (P : Finset ℕ) (r : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    |roughCharacterDensityTruncation P r - roughCharacterEulerDensity P| ≤
      ∑ S ∈ P.powersetCard (r + 1), 1 / (roughSubsetDivisor S : ℝ) := by
  rw [roughCharacterDensityTruncation_eq, rough_layer_reciprocal_mass_eq]
  let g : ℕ → ℝ := fun p => 1 / (p : ℝ)
  have hg0 : ∀ p ∈ P, 0 ≤ g p := fun _ _ => by dsimp [g]; positivity
  have hg1 : ∀ p ∈ P, g p ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    exact (div_le_one hp0).mpr (by exact_mod_cast (hprime p hp).one_le)
  have hmod := Nat.mod_two_eq_zero_or_one r
  rcases hmod with hmod | hmod
  · have hr : r = 2 * (r / 2) := by omega
    have hb := densityPolynomial_bounds P g hg0 hg1 (r / 2)
    change |densityPolynomial r P g - (∏ p ∈ P, (1 - g p))| ≤ elementarySum P g (r + 1)
    rw [hr, abs_of_nonneg (sub_nonneg.mpr hb.2)]
    calc
      _ ≤ densityPolynomial (2 * (r / 2)) P g -
          densityPolynomial (2 * (r / 2) + 1) P g := sub_le_sub_left hb.1 _
      _ = _ := densityPolynomial_gap (r / 2) P g
  · have hr : r = 2 * (r / 2) + 1 := by omega
    have hb := densityPolynomial_bounds P g hg0 hg1 (r / 2)
    have hnext := (densityPolynomial_bounds P g hg0 hg1 (r / 2 + 1)).2
    change |densityPolynomial r P g - (∏ p ∈ P, (1 - g p))| ≤ elementarySum P g (r + 1)
    rw [hr, abs_of_nonpos (sub_nonpos.mpr hb.1), neg_sub]
    calc
      _ ≤ densityPolynomial (2 * (r / 2 + 1)) P g -
          densityPolynomial (2 * (r / 2) + 1) P g := sub_le_sub_right hnext _
      _ = _ := by
        rw [show 2 * (r / 2 + 1) = (2 * (r / 2) + 1) + 1 by omega,
          densityPolynomial_succ]
        norm_num [pow_add, pow_mul]

/-- The finite endpoint count of all retained squarefree divisors. -/
theorem roughTruncationSubsets_card_le_pow (P : Finset ℕ) (r v : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hheight : ∀ p ∈ P, p ≤ v) (hv : 1 ≤ v) :
    (roughTruncationSubsets P r).card ≤ (r + 1) * v ^ r := by
  calc
    _ = ∑ j ∈ range (r + 1), (P.powersetCard j).card := by
      simpa using sum_roughTruncationSubsets P r (fun _ => (1 : ℕ))
    _ ≤ ∑ j ∈ range (r + 1), v ^ r := by
      apply sum_le_sum
      intro j hj
      exact (rough_layer_card_le_pow P j v hprime hheight).trans
        (Nat.pow_le_pow_right hv (Nat.le_of_lt_succ (mem_range.mp hj)))
    _ = _ := by simp

end ArtinMatthews
