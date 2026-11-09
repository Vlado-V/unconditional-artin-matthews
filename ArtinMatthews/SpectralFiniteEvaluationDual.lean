module

public import ArtinMatthews.SpectralGamma0EigenPlaneBound


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
