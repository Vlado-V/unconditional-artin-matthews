module

public import ArtinMatthews.MarkedMajorMellinLabelEnergyData
public import ArtinMatthews.MarkedMajorMellinLabelEnergyParameters


set_option backward.privateInPublic true
@[expose] public section

/-! Actual central cancellation at the enlarged radius used by Mellin separation. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped ContDiff

theorem markedMajorLabelEnergy_central
    (cfg : MarkedMajorLabelEnergyConfig)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (σ Kx B P : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℝ, 1 ≤ X → X ≤ Real.exp (σ*L) → X ≤ Kx*Real.exp L →
      ∀ {J : Type} [Fintype J] [DecidableEq J] (z : MarkedMajorLabelEnergyData J cfg L X),
      (∫ t in Set.Icc (-(2*X*L^B)) (2*X*L^B), ‖z.endpoint cutoff t‖^2) ≤ L^(-P) ∧
      (∫ t in Set.Icc (-(2*X*L^B)) (2*X*L^B), ‖z.conjugateEndpoint cutoff t‖^2) ≤ L^(-P) := by
  have hmain := marked_major_label_cancellation cutoff hcutoff hlo hhi hsupp
    cfg.c cfg.C₁ (σ+1) cfg.d cfg.a cfg.η cfg.τ cfg.C B (2*Kx) σ (B+1) cfg.D P cfg.A₀ cfg.Kθ cfg.v₀
    cfg.hc cfg.hC₁ (by linarith) cfg.hd cfg.ha cfg.hη cfg.hτ cfg.hC hσ (by linarith)
    cfg.hD hP cfg.hA₀ cfg.hKθ cfg.hv₀
  have hconj := marked_major_label_conjugate_cancellation cutoff hcutoff hlo hhi hsupp
    cfg.c cfg.C₁ (σ+1) cfg.d cfg.a cfg.η cfg.τ cfg.C B (2*Kx) σ (B+1) cfg.D P cfg.A₀ cfg.Kθ cfg.v₀
    cfg.hc cfg.hC₁ (by linarith) cfg.hd cfg.ha cfg.hη cfg.hτ cfg.hC hσ (by linarith)
    cfg.hD hP cfg.hA₀ cfg.hKθ cfg.hv₀
  filter_upwards [hmain,hconj,markedMajorLabelEnergy_height_parameters B σ Kx hB] with L hm hc hp
  intro X hX hupper hcomp J _ _ z
  let : NeZero z.q := ⟨z.q_ne_zero⟩
  obtain ⟨hT,hlog,hTU,hTR⟩ := hp X hX hupper hcomp
  have hHU : z.H*z.U ≤ Real.exp (σ*L) := z.product_eq.trans_le hupper
  have hratio : (2*X*L^B)/(z.H*z.U) ≤ L^(B+1) := by simpa only [z.product_eq] using hTR
  have h₁ := hm z.P₀ z.bands z.first_prime z.bands_prime z.first_disjoint z.bands_disjoint
    z.first_mass z.bands_mass z.first_lower z.first_upper z.Y z.θ (2*X*L^B) z.H z.u z.v z.U z.l z.r z.β
    z.Y_pos z.theta_bound hT hlog hTU z.H_lower z.H_le_u z.u_le_v z.v_le_two_H z.v_upper
    z.U_lower z.U_le_l z.r_le_two_U hHU hratio z.coefficient_bound z.q z.χ z.modulation
    z.modulus_bound z.modulation_bound z.k z.χb
  have h₂ := hc z.P₀ z.bands z.first_prime z.bands_prime z.first_disjoint z.bands_disjoint
    z.first_mass z.bands_mass z.first_lower z.first_upper z.Y z.θ (2*X*L^B) z.H z.u z.v z.U z.l z.r z.β
    z.Y_pos z.theta_bound hT hlog hTU z.H_lower z.H_le_u z.u_le_v z.v_le_two_H z.v_upper
    z.U_lower z.U_le_l z.r_le_two_U hHU hratio z.coefficient_bound z.q z.χ z.modulation
    z.modulus_bound z.modulation_bound z.k z.χb
  constructor
  · dsimp [MarkedMajorLabelEnergyData.endpoint,MarkedMajorLabelEnergyData.allBands,
      markedMajorLabelEndpoint]
    exact h₁
  · dsimp [MarkedMajorLabelEnergyData.conjugateEndpoint,MarkedMajorLabelEnergyData.allBands,
      markedMajorLabelConjugateEndpoint]
    exact h₂

end ArtinMatthews
