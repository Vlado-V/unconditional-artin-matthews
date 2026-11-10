module

public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.MarkedMemoryGoodBoundary
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

/-! Cauchy for two independently bounded endpoint vectors. A bounded
initial birth phase changes only the left vector; the right vector keeps
its original literal empty-memory boundary. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedWeightedBoundary_two_sided_norm_le {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ s, 0 ≤ μ s) (b₀ b₁ f : Ω → ℂ)
    {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hb₀ : (∑ s, μ s*‖b₀ s‖^2) ≤ D) (hb₁ : (∑ s, μ s*‖b₁ s‖^2) ≤ D)
    (hf : (∑ s, μ s*‖f s‖^2) ≤ C^2*∑ s, μ s*‖b₁ s‖^2) :
    ‖∑ s, (μ s:ℂ)*star (b₀ s)*f s‖ ≤ D*C := by
  have hE₀ : 0 ≤ ∑ s, μ s*‖b₀ s‖^2 := Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  have hE₁ : 0 ≤ ∑ s, μ s*‖b₁ s‖^2 := Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD hC)).mp
  calc
    _ ≤ (∑ s, μ s*‖b₀ s‖^2)*(∑ s, μ s*‖f s‖^2) := markedWeightedBoundary_cauchy μ hμ b₀ f
    _ ≤ (∑ s, μ s*‖b₀ s‖^2)*(C^2*∑ s, μ s*‖b₁ s‖^2) := mul_le_mul_of_nonneg_left hf hE₀
    _ ≤ D*(C^2*D) := mul_le_mul hb₀ (mul_le_mul_of_nonneg_left hb₁ (sq_nonneg _))
      (mul_nonneg (sq_nonneg C) hE₁) hD
    _ = _ := by ring

theorem markedWeightedEnergy_bounded_multiplier {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ s, 0 ≤ μ s) (β f : Ω → ℂ) (hβ : ∀ s, ‖β s‖ ≤ 1) :
    (∑ s, μ s*‖β s*f s‖^2) ≤ ∑ s, μ s*‖f s‖^2 := by
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (hμ s)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hβ s) (norm_nonneg _)).trans_eq (one_mul _)

end ArtinMatthews
