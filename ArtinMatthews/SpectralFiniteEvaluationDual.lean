module

public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! Finite real-coefficient duality bounds the full complex evaluation square sum. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews

private theorem finite_projection_sq_le_of_real_sum_bound {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (C : ℝ) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ w, ‖L w‖ ≤ ‖w‖)
    (hb : ∀ c : ι → ℝ, ‖∑ i ∈ s, c i • z i‖^2 ≤ C^2*(∑ i ∈ s, (c i)^2)) :
    (∑ i ∈ s, (L (z i))^2) ≤ C^2 := by
  let c : ι → ℝ := fun i => L (z i)
  let S : ℝ := ∑ i ∈ s, (c i)^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : L (∑ i ∈ s, c i • z i) = S := by
    rw [map_sum]
    change (∑ i ∈ s, L (c i • z i)) = _
    simp only [map_smul,smul_eq_mul]
    simp only [c,S,pow_two]
  have hL' := hL (∑ i ∈ s, c i • z i)
  rw [he,Real.norm_of_nonneg hS] at hL'
  have hsq : S^2 ≤ C^2*S :=
    ((sq_le_sq₀ hS (norm_nonneg _)).mpr hL').trans (hb c)
  by_cases hz : S = 0
  · change S ≤ C^2
    rw [hz]
    exact sq_nonneg C
  · have hp : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    change S ≤ C^2
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using hsq) hp

theorem finite_complex_evaluation_sq_le_of_real_sum_bound {ι : Type*}
    (s : Finset ι) (z : ι → ℂ) (C : ℝ)
    (hb : ∀ c : ι → ℝ, ‖∑ i ∈ s, c i • z i‖^2 ≤ C^2*(∑ i ∈ s, (c i)^2)) :
    (∑ i ∈ s, ‖z i‖^2) ≤ 2*C^2 := by
  have hr := finite_projection_sq_le_of_real_sum_bound s z C Complex.reCLM
    (fun w => by simpa only [Real.norm_eq_abs,Complex.reCLM_apply] using Complex.abs_re_le_norm w) hb
  have hi := finite_projection_sq_le_of_real_sum_bound s z C Complex.imCLM
    (fun w => by simpa only [Real.norm_eq_abs,Complex.imCLM_apply] using Complex.abs_im_le_norm w) hb
  have he : (∑ i ∈ s, ‖z i‖^2) =
      (∑ i ∈ s, (Complex.reCLM (z i))^2)+(∑ i ∈ s, (Complex.imCLM (z i))^2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Complex.normSq_apply,Complex.reCLM_apply,Complex.imCLM_apply,pow_two] using Complex.sq_norm (z i)
  rw [he]
  linarith

end ArtinMatthews
