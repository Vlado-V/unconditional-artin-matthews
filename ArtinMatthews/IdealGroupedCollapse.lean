module

public import ArtinMatthews.IdealGroupedBudget
public import ArtinMatthews.IdealFiberCollapse
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

/-! Arbitrary ordered-tuple tests collapse to numeric coefficients with
the actual factorial harmonic atom budget. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem idealGroupedCollapse_energy_le (P : G → Finset ℕ) (k : G → ℕ)
    (hP : ∀ g p, p ∈ P g → p.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    (hV : ∀ g, 0 < bandReciprocalMass (P g))
    (f : IdealGroupedLabels P k → ℂ) (S : Finset ℕ) {U : ℝ} (hU : 0 < U)
    (hS : ∀ n ∈ S, U ≤ (n : ℝ)) :
    (∑ n ∈ S, ‖idealFiberCoefficient (idealGroupedMass P k) idealGroupedProduct f n‖^2) ≤
      (idealGroupedAtomBudget P k / U) * idealFrameEnergy (idealGroupedMass P k) f := by
  have hbudget : 0 ≤ idealGroupedAtomBudget P k := by
    unfold idealGroupedAtomBudget
    exact prod_nonneg fun g _ => mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (inv_nonneg.mpr (hV g).le) _)
  apply idealFiberCoefficient_energy_le _ (idealGroupedMass_nonneg P k hV) _ f S
    (div_nonneg hbudget hU.le)
  intro n hn
  change idealGroupedProductMass P k n ≤ _
  exact (idealGroupedProductMass_le P k hP hdis hV n).trans
    (div_le_div_of_nonneg_left hbudget hU (hS n hn))

theorem idealGroupedCollapse_power (P : G → Finset ℕ) (k : G → ℕ)
    (hP : ∀ g p, p ∈ P g → p.Prime)
    (hdis : Pairwise (fun g h => Disjoint (P g) (P h)))
    {m : ℕ} {C₀ v₀ L U : ℝ} (hv₀ : 0 < v₀) (hL : 1 ≤ L) (hU : 0 < U)
    (hV : ∀ g, v₀ ≤ bandReciprocalMass (P g)) (hk : ∀ g, k g ≤ m)
    (hcard : (Fintype.card G : ℝ) ≤ C₀*Real.log L)
    (f : IdealGroupedLabels P k → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, U ≤ (n : ℝ)) :
    (∑ n ∈ S, ‖idealFiberCoefficient (idealGroupedMass P k) idealGroupedProduct f n‖^2) ≤
      (L^(idealGroupedBudgetExponent m C₀ v₀)/U) * idealFrameEnergy (idealGroupedMass P k) f := by
  have hVpos : ∀ g, 0 < bandReciprocalMass (P g) := fun g => hv₀.trans_le (hV g)
  exact (idealGroupedCollapse_energy_le P k hP hdis hVpos f S hU hS).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (idealGroupedAtomBudget_power P k hv₀ hL hV hk hcard) hU.le)
      (idealFrameEnergy_nonneg _ (idealGroupedMass_nonneg P k hVpos) f))

end
end ArtinMatthews
