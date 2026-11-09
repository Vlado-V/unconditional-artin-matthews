module

public import ArtinMatthews.MarkedMajorMellinLabelEnergyData


set_option backward.privateInPublic true
@[expose] public section

/-! Both actual endpoint weighted means with a common uniform constant. -/
namespace ArtinMatthews
open Filter MeasureTheory

theorem markedMajorLabelEnergy_weighted
    (cfg : MarkedMajorLabelEnergyConfig) (σ hi : ℝ) (hσ : 0 ≤ σ) (hhi : 0 ≤ hi)
    (cutoff : ℝ → ℂ) (hcutoff : ∀ y, ‖cutoff y‖ ≤ 1)
    (hsupp : Function.support cutoff ⊆ Set.Iic hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ X : ℝ, 1 ≤ X → X ≤ Real.exp (σ*L) →
      ∀ {J : Type} [Fintype J] (z : MarkedMajorLabelEnergyData J cfg L X)
      (W c : ℝ), 1 ≤ W →
      (∫ t : ℝ, markedMajorFourierWeight (W*X) 2 (t-c)*‖z.endpoint cutoff t‖^2) ≤ C*W*L^(2*cfg.D+5) ∧
      (∫ t : ℝ, markedMajorFourierWeight (W*X) 2 (t-c)*‖z.conjugateEndpoint cutoff t‖^2) ≤ C*W*L^(2*cfg.D+5) := by
  obtain ⟨C₁,hC₁,hmean⟩ := marked_major_label_weighted_scaled_mean σ cfg.D hi hσ hhi cutoff hcutoff hsupp
  obtain ⟨C₂,hC₂,hconj⟩ := marked_major_label_conjugate_weighted_scaled_mean σ cfg.D hi hσ hhi cutoff hcutoff hsupp
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hmean,hconj,eventually_ge_atTop (1/cfg.τ),eventually_ge_atTop (1:ℝ)]
    with L hm hc hτL hL
  intro X hX hupper J _ z W c hW
  have hH : 0 < z.H := z.H_pos
  have hU : 0 < z.U := z.U_pos
  have hlog : 1 ≤ Real.log z.u := by
    have hτ : 1 ≤ cfg.τ*L := by
      have h := (div_le_iff₀ cfg.hτ).mp hτL
      nlinarith
    exact hτ.trans ((Real.le_log_iff_exp_le (hH.trans_le z.H_le_u)).mpr
      (z.H_lower.trans z.H_le_u))
  have hprod : 1 ≤ z.H*z.U := by simpa only [z.product_eq] using hX
  have hprodUpper : z.H*z.U ≤ Real.exp (σ*L) := z.product_eq.trans_le hupper
  have h₁ := hm z.allBands z.allBands_prime z.allBands_disjoint z.allBands_mass
    z.Y z.θ z.H z.u z.v z.U z.l z.r z.β z.Y_pos hH hU hprod hprodUpper z.H_le_u z.v_le_two_H
    hlog z.U_le_l z.r_le_two_U z.coefficient_bound z.k z.q z.χb z.χ z.modulation c W hW 2 (by norm_num)
  have h₂ := hc z.allBands z.allBands_prime z.allBands_disjoint z.allBands_mass
    z.Y z.θ z.H z.u z.v z.U z.l z.r z.β z.Y_pos hH hU hprod hprodUpper z.H_le_u z.v_le_two_H
    hlog z.U_le_l z.r_le_two_U z.coefficient_bound z.k z.q z.χb z.χ z.modulation c W hW 2 (by norm_num)
  have hCW (C : ℝ) (hC : C ≤ max C₁ C₂) : C*W*L^(2*cfg.D+5) ≤ max C₁ C₂*W*L^(2*cfg.D+5) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by linarith))
      (Real.rpow_nonneg (by linarith : 0 ≤ L) _)
  constructor
  · calc
      _ ≤ C₁*W*L^(2*cfg.D+5) := by
        simpa only [MarkedMajorLabelEnergyData.endpoint,z.product_eq] using h₁
      _ ≤ _ := hCW C₁ (le_max_left _ _)
  · calc
      _ ≤ C₂*W*L^(2*cfg.D+5) := by
        simpa only [MarkedMajorLabelEnergyData.conjugateEndpoint,z.product_eq] using h₂
      _ ≤ _ := hCW C₂ (le_max_right _ _)

end ArtinMatthews
