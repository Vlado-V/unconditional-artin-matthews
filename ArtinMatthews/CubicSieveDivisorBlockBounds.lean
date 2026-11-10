module

public import ArtinMatthews.CubicSieveBlockProducts
public import ArtinMatthews.CubicSieveDivisorModelNormalized
public import ArtinMatthews.CubicSieveBlockHarmonic
public import ArtinMatthews.CubicSieveBlockRelative
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

/-! Specialization of all relative estimates to the actual divisor factors. -/

noncomputable section
namespace ArtinMatthews

open Finset OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

theorem cubicSieve_divisorBlock_relative_data {z A : ℝ} (hz : 1 < z) (hA : 0 ≤ A)
    (m j : ℕ) (hmass : (∑ p ∈ cubicSieveBlock z j, cubicSievePrimeDivisorDensity p) ≤ A) :
    let C := Real.exp (12 * A)
    0 ≤ cubicSieveDivisorBlockUpperRatio z m j 1 ∧
      cubicSieveDivisorBlockUpperRatio z m j 1 ≤ 1 + C * cubicSieveBlockLoss m j ∧
      0 ≤ cubicSieveDivisorBlockOverflowRatio z m j 1 ∧
      cubicSieveDivisorBlockOverflowRatio z m j 1 ≤ C * cubicSieveBlockLoss m j ∧
      |cubicSieveDivisorBlockUpperTangent z m j| ≤ 2 * C * Real.log z * (1 / 2 : ℝ) ^ j ∧
      |cubicSieveDivisorBlockOverflowTangent z m j| ≤
        Real.log z * (1 / 2 : ℝ) ^ j * C * cubicSieveBlockLoss m j := by
  let P := cubicSieveBlock z j
  let g (p : ℕ) := cubicSievePrimeDivisorModel 1 p
  let v := cubicSievePrimeDivisorDensityDerivative
  let L := Real.log z * (1 / 2 : ℝ) ^ j
  let E := cubicSieveDivisorBlockEuler z j
  have hL : 0 ≤ L := mul_nonneg (Real.log_pos hz).le (by positivity)
  have hp (p : ℕ) (hp : p ∈ P) : p.Prime := (mem_cubicSieveBlock hz |>.mp hp).1
  have he (p : ℕ) (hp' : p ∈ P) : g p = cubicSievePrimeDivisorDensity p :=
    cubicSieve_primeDivisorModel_one (hp p hp').pos
  have h₀ (p : ℕ) (hp' : p ∈ P) : 0 ≤ g p := by
    rw [he p hp']
    exact (cubicSieve_primeDivisorDensity_bounds (hp p hp')).1
  have hcap (p : ℕ) (hp' : p ∈ P) : g p ≤ 3 / 4 := by
    rw [he p hp']
    exact (cubicSieve_primeDivisorDensity_bounds (hp p hp')).2.1
  have hv (p : ℕ) (hp' : p ∈ P) : |v p| ≤ L * g p :=
    (cubicSieve_primeDivisorDensityDerivative_abs_le (hp p hp')).trans (by
      rw [he p hp']
      exact mul_le_mul_of_nonneg_right (cubicSieve_block_prime_log_le hz hp')
        (cubicSieve_primeDivisorDensity_bounds (hp p hp')).1)
  have hsum : (∑ p ∈ P, g p) ≤ A :=
    (sum_congr rfl he).trans_le hmass
  have hE : 0 < E := (Real.exp_pos _).trans_le (cubicSieve_blockEuler_lower P g h₀ hcap hsum)
  have hU := cubicSieve_upperPolynomial_relative_bound P g hA h₀ hcap hsum (cubicSieveOrder m j)
  refine ⟨hU.1, hU.2, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (BonferroniDensity.elementarySum_nonneg P g h₀ _) hE.le
  · exact cubicSieve_elementary_relative_bound P g hA h₀ hcap hsum _
  · unfold cubicSieveDivisorBlockUpperTangent
    rw [abs_div, abs_of_pos hE]
    exact (cubicSieve_polynomialTangent_relative_bound P g v hA hL h₀ hcap hv hsum _).trans_eq
      (by unfold L; ring)
  · unfold cubicSieveDivisorBlockOverflowTangent
    rw [abs_div, abs_of_pos hE]
    exact cubicSieve_elementaryTangent_relative_bound P g v hA hL h₀ hcap hv hsum _

end ArtinMatthews
