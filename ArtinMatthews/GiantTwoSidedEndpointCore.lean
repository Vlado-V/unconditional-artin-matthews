module

public import ArtinMatthews.GiantCandidateAllocationCore
public import ArtinMatthews.GiantCandidateSquareCore
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
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

/-! The actual right endpoint has the ordered-fiber bound at the
stripped product itself. A fixed Dirichlet character retains this
bound, including at nonunits. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateAllocationCore_actual_norm_le_stripped_fiber (γ : ℝ) (hγ : 0 < γ)
    (j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ (C P : Finset ℕ) (n : ℕ),
      ‖giantCandidateAllocationCore C P (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n‖ ≤
        ((giantOrderedProductFiber j (giantCandidateStrip P n)).card:ℝ) := by
  filter_upwards [giantCandidateStrippedSlotCoefficient_actual_norm_le_one γ hγ] with x hx
  intro C P n
  let E := giantOrderedProductFiber j (giantCandidateStrip P n)
  let a := giantCandidateStrippedSlotCoefficient C (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ)
  change ‖∑ t ∈ E,∏ i,a (t i)‖ ≤ _
  calc
    _ ≤ ∑ t ∈ E,‖∏ i,a (t i)‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ E,(1:ℝ) := by
      apply sum_le_sum
      intro t _
      rw [norm_prod]
      exact prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hx C (t i))
    _ = _ := by simp only [E,sum_const,nsmul_eq_mul,mul_one]

theorem giantCandidateAllocationCore_character_actual_norm_le_stripped_fiber
    {m : ℕ} (χ : DirichletCharacter ℂ m) (γ : ℝ) (hγ : 0 < γ) (j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ (C P : Finset ℕ) (n : ℕ),
      ‖χ n*giantCandidateAllocationCore C P (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n‖ ≤
        ((giantOrderedProductFiber j (giantCandidateStrip P n)).card:ℝ) := by
  filter_upwards [giantCandidateAllocationCore_actual_norm_le_stripped_fiber γ hγ j] with x hx
  intro C P n
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (hx C P n)

end
end ArtinMatthews
