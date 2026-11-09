module

public import ArtinMatthews.MarkedMajorLabelFullSource
public import ArtinMatthews.MarkedMajorMellinLabelEnergy


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Finset Filter
open scoped ContDiff
noncomputable section

namespace MarkedMajorLabelEnergyData

/-- The original finite two-endpoint source after fixing the characters. -/
def source {J J' : Type} [Fintype J] [Fintype J']
    {cfg : MarkedMajorLabelEnergyConfig} {L X : ℝ}
    (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J' cfg L X)
    (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (theta : ℝ) : ℂ :=
  (z.Y:ℂ)⁻¹*∑ v ∈ markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r,
    ∑ v' ∈ markedMajorLabelTripleSet z'.allBands z'.u z'.v z'.l z'.r,
    (markedMajorLabelTripleCoefficient z.allBands cutoff z.χb z.θ z.Y z.χ
      (Real.exp (L^(6/25:ℝ))) z.modulation z.β v*
     markedMajorLabelConjugateTripleCoefficient z'.allBands cutoff z'.χb z'.θ z'.Y z'.χ
      (Real.exp (L^(6/25:ℝ))) z'.modulation z'.β v')*
    (ψ ((markedMajorLabelTripleValue v-markedMajorLabelTripleValue v')/z.Y)*
      OAI.Problem337.RealPhase.phase (theta*((markedMajorLabelTripleValue v-markedMajorLabelTripleValue v')/z.Y)))

end MarkedMajorLabelEnergyData

theorem markedMajor_source_difference {X Y : ℝ} (hX : X ≠ 0) (hY : Y ≠ 0) (v w : ℝ) :
    X*(v/(Y*X)-w/(Y*X)) = (v-w)/Y := by
  field_simp

/-- The literal fixed-character major source has arbitrary logarithmic saving.
No endpoint energy or abstract cancellation hypothesis is assumed. -/
theorem markedMajorLabelEnergy_source_all_log
    (cfg : MarkedMajorLabelEnergyConfig) (σ Kx : ℝ) (hσ : 0 ≤ σ)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y, ‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo < 4*hi)
    (hsupp : Function.support cutoff ⊆ Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Icc (-R) R) (P : ℝ) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℝ, 1 ≤ X → X ≤ Real.exp (σ*L) → X ≤ Kx*Real.exp L →
      ∀ {J J' : Type} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
      (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J' cfg L X),
      z'.Y=z.Y → ∀ theta : ℝ, |theta| ≤ cfg.Kθ*L^cfg.A₀ →
      ‖z.source z' cutoff ψ theta‖ ≤ (z.Y*X)*L^(-P) := by
  filter_upwards [markedMajorMellinLabelEnergy_all_log cfg σ Kx hσ cutoff hcutoff hnorm
    hlo hhi hsupp ψ hlo hinterval hψ P hP] with L hL
  intro X hX1 hupper hcomp J J' _ _ _ _ z z' hY theta htheta
  have hX : 0 < X := by linarith
  have H := markedMajorLabel_full_source_energy z.allBands z'.allBands z.allBands_prime z'.allBands_prime
    cutoff hlo hinterval hsupp z.χb z'.χb z.χ z'.χ z.θ z'.θ theta z.Y
    (Real.exp (L^(6/25:ℝ))) X z.H z.u z.v z.U z'.H z'.u z'.v z'.U z.modulation z'.modulation
    z.l z.r z'.l z'.r z.β z'.β z.Y_pos hX z.H_pos z.U_pos z'.H_pos z'.U_pos
    z.product_eq z'.product_eq z.H_le_u z.u_le_v z.v_le_two_H z.U_le_l z.r_le_two_U
    z'.H_le_u z'.u_le_v z'.v_le_two_H z'.U_le_l z'.r_le_two_U ψ hψ
  have he := hL X hX1 hX hupper hcomp z z' theta htheta
  have hbound := mul_le_mul_of_nonneg_left he (mul_pos z.Y_pos hX).le
  simp only [MarkedMajorLabelEnergyData.endpoint,MarkedMajorLabelEnergyData.conjugateEndpoint,hY] at hbound
  have H' := H.trans hbound
  simpa only [MarkedMajorLabelEnergyData.source,hY,
    markedMajor_source_difference hX.ne' z.Y_pos.ne'] using H'

end
end ArtinMatthews
