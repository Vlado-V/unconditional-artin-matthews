module

public import ArtinMatthews.IdealFiniteFrame


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
