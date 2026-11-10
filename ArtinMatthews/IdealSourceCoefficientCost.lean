module

public import ArtinMatthews.IdealSourceParameterDefinitions
public import ArtinMatthews.IdealSourceBlocks
public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealResidualPolynomialCost
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The literal signed residual family has a fixed coefficient cost
after the source parameters are selected, uniformly in the copied dimension. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealSource_scalar_cost {E C₀ v₀ d C L : ℝ} {m b P : ℕ}
    (hE : 0 ≤ E) (hC₀ : 0 ≤ C₀) (hd : 0 ≤ d) (hC : 0 ≤ C) (hL : 2 ≤ L)
    (hb : (b : ℝ) ≤ C₀*Real.log L) (hP : P ≤ m*b) :
    (1+(2 : ℝ)^P)*
      (1+(((⌊L^(idealSourceRationalExponent E C₀ v₀ d m)⌋₊ : ℕ) : ℝ)^2/
        L^(-idealSourceThresholdExponent E C₀ v₀ d C m))^2) ≤
      L^(idealSourceCostExponent E C₀ v₀ d C m) := by
  have hp := idealSourceParameters_nonnegative (v₀ := v₀) hE hC₀ hd hC m
  apply idealResidualScalarCost_bound L ((m : ℝ)*C₀)
    (idealSourceRationalExponent E C₀ v₀ d m) (idealSourceThresholdExponent E C₀ v₀ d C m) P
    hL (mul_nonneg (Nat.cast_nonneg _) hC₀) hp.2.1 hp.2.2.2.1
  calc
    _ ≤ (m : ℝ)*(b : ℝ) := by exact_mod_cast hP
    _ ≤ (m : ℝ)*(C₀*Real.log L) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by ring

theorem idealSource_coefficient_cost {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (S T U : Finset G) {m J ell : ℕ} (hm : m ≤ J)
    (hST : Disjoint S T) (hU : S ∪ T = U)
    {E C₀ v₀ d C L : ℝ} (hE : 0 ≤ E) (hC₀ : 0 ≤ C₀) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (hL : 2 ≤ L) (hcard : (U.card : ℝ) ≤ C₀*Real.log L)
    (s t : IdealResidualPattern G J → MarkedPhysicalMarking P (J+ell))
    (aux : ∀ ν, GiantTwoSidedPatternAuxiliary P (idealResidualCopied ν)) :
    (∑ ν ∈ idealResidualPatterns (idealSourceProbes S hm) (idealSourceProbes T hm),
      ‖idealResidualCoefficient P ⌊L^(idealSourceRationalExponent E C₀ v₀ d m)⌋₊
        (L^(-idealSourceWidthExponent E C₀ v₀ d C m))
        (L^(-idealSourceThresholdExponent E C₀ v₀ d C m)) ν (s ν) (t ν) (aux ν)‖) ≤
      L^(idealSourceCostExponent E C₀ v₀ d C m) := by
  have hp := idealSourceParameters_nonnegative (v₀ := v₀) hE hC₀ hd hC m
  have hcount : (((idealSourceProbes S hm).card+(idealSourceProbes T hm).card : ℕ) : ℝ) ≤
      ((m : ℝ)*C₀)*Real.log L := by
    rw [idealSourceProbes_total_card S T U hm hST hU, Nat.cast_mul]
    have h := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    nlinarith
  exact idealResidualCoefficient_polynomial_cost P (idealSourceProbes S hm) (idealSourceProbes T hm)
    L ((m : ℝ)*C₀) (idealSourceRationalExponent E C₀ v₀ d m)
    (idealSourceThresholdExponent E C₀ v₀ d C m) (L^(-idealSourceWidthExponent E C₀ v₀ d C m))
    hL (mul_nonneg (Nat.cast_nonneg _) hC₀) hp.2.1 hp.2.2.2.1 hcount s t aux

end
end ArtinMatthews
