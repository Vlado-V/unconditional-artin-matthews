module

public import ArtinMatthews.IdealFiniteFrame
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The conditional character-frame operator has the same Gram bound
as its synthesis map, without a cell-count loss. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω C : Type*} [Fintype Ω] [Fintype C]

def idealFrameApply (μ : Ω → ℝ) (φ : C → Ω → ℂ) (f : Ω → ℂ) : Ω → ℂ :=
  idealFrameSynthesis φ (idealFrameCoefficient μ φ f)

theorem idealFrameCoefficient_square_identity (μ : Ω → ℝ)
    (φ : C → Ω → ℂ) (f : Ω → ℂ) :
    ((∑ c, ‖idealFrameCoefficient μ φ f c‖^2 : ℝ) : ℂ) =
      ∑ x, (μ x : ℂ) * star (idealFrameApply μ φ f x) * f x := by
  let a := idealFrameCoefficient μ φ f
  calc
    _ = ∑ c, star (a c) * a c := by
      push_cast
      apply sum_congr rfl
      intro c _
      exact (Complex.conj_mul' (a c)).symm
    _ = ∑ c, star (a c) * ∑ x, (μ x : ℂ) * star (φ c x) * f x := rfl
    _ = ∑ x, ∑ c, star (a c) * ((μ x : ℂ) * star (φ c x) * f x) := by
      simp only [mul_sum]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro x _
      simp only [idealFrameApply, idealFrameSynthesis, star_sum, star_mul, mul_sum, sum_mul]
      apply sum_congr rfl
      intro c _
      change star (a c) * ((μ x : ℂ) * star (φ c x) * f x) =
        (μ x : ℂ) * (star (φ c x) * star (a c)) * f x
      ring

theorem idealFrameCoefficient_energy_le (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (φ : C → Ω → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ c, (∑ d, ‖idealFrameGram μ φ c d‖) ≤ B) (f : Ω → ℂ) :
    (∑ c, ‖idealFrameCoefficient μ φ f c‖^2) ≤ B * idealFrameEnergy μ f := by
  let S : ℝ := ∑ c, ‖idealFrameCoefficient μ φ f c‖^2
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hf : 0 ≤ idealFrameEnergy μ f := idealFrameEnergy_nonneg μ hμ f
  have hsynth := idealFrameSynthesis_energy_le μ hμ φ B hrow (idealFrameCoefficient μ φ f)
  have hc := idealFrame_weighted_cauchy μ hμ (idealFrameApply μ φ f) f
  rw [← idealFrameCoefficient_square_identity, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hS] at hc
  by_cases hzero : S = 0
  · change S ≤ _
    rw [hzero]
    exact mul_nonneg hB hf
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    have hineq : S*S ≤ S*(B*idealFrameEnergy μ f) := by
      calc
        _ = S^2 := (pow_two _).symm
        _ ≤ idealFrameEnergy μ (idealFrameApply μ φ f) * idealFrameEnergy μ f := hc
        _ ≤ (B*S)*idealFrameEnergy μ f := mul_le_mul_of_nonneg_right hsynth hf
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ hSpos).mp hineq

theorem idealFrameApply_energy_le (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (φ : C → Ω → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hrow : ∀ c, (∑ d, ‖idealFrameGram μ φ c d‖) ≤ B) (f : Ω → ℂ) :
    idealFrameEnergy μ (idealFrameApply μ φ f) ≤ B^2 * idealFrameEnergy μ f := by
  calc
    _ ≤ B * ∑ c, ‖idealFrameCoefficient μ φ f c‖^2 :=
      idealFrameSynthesis_energy_le μ hμ φ B hrow _
    _ ≤ B * (B * idealFrameEnergy μ f) :=
      mul_le_mul_of_nonneg_left (idealFrameCoefficient_energy_le μ hμ φ hB hrow f) hB
    _ = _ := by ring

end
end ArtinMatthews
