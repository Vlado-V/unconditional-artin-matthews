module

public import ArtinMatthews.CircleDetector
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! Exact finite-sum comparison between an integer equation and the weighted
circle detector. Its error uses the actual coefficient l1 mass.
-/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem circleDetector_finite_approximation {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (frequency : ι → ℤ) (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ q∈Q, 0≤ω q) (hΛ : 0<circleNormalizer Q ω)
    (R : ℕ) (hR : ∀ i∈S, (frequency i).natAbs≤R) :
    ‖(∑ i∈S, a i*circleDetector Q ω (frequency i)) -
      (∑ i∈S with frequency i=0, a i)‖ ≤
    (∑ i∈S, ‖a i‖) * (circleWeightMass Q ω*(R : ℝ)^2/circleNormalizer Q ω) := by
  classical
  have heq : (∑ i∈S, a i*circleDetector Q ω (frequency i)) -
      (∑ i∈S with frequency i=0, a i) =
      ∑ i∈S, a i*(circleDetector Q ω (frequency i) -
        (if frequency i=0 then 1 else 0)) := by
    rw [Finset.sum_filter,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    split_ifs <;> ring
  rw [heq]
  calc
    _ ≤ ∑ i∈S, ‖a i*(circleDetector Q ω (frequency i) -
        (if frequency i=0 then 1 else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ i∈S, ‖a i‖*(circleWeightMass Q ω*(R : ℝ)^2/circleNormalizer Q ω) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (circleDetector_error_le Q ω hω hΛ R
        (frequency i) (hR i hi)) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

end ArtinMatthews
