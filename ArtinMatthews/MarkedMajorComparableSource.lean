module

public import ArtinMatthews.MarkedMajorComparableFullSource
public import ArtinMatthews.MarkedMajorLabelEnergySource
public import ArtinMatthews.MarkedMajorComparableEnergy


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Finset Filter
open scoped ContDiff
noncomputable section

namespace MarkedMajorLabelEnergyData

/-- The original finite two-endpoint source after fixing the characters. -/
def comparableSource {J J' : Type} [Fintype J] [Fintype J']
    {cfg : MarkedMajorLabelEnergyConfig} {L X X' : ℝ}
    (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J' cfg L X')
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

/-- The literal fixed-character major source has arbitrary logarithmic saving.
No endpoint energy or abstract cancellation hypothesis is assumed. -/
theorem markedMajorLabelEnergy_comparable_source_all_log
    (cfg : MarkedMajorLabelEnergyConfig) (σ Kx : ℝ) (hσ : 0 ≤ σ)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y, ‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo/2 < 8*hi)
    (hsupp : Function.support cutoff ⊆ Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Icc (-R) R) (P : ℝ) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop, ∀ X X' : ℝ, 1 ≤ X → 1 ≤ X' → X ≤ Real.exp (σ*L) → X ≤ Kx*Real.exp L →
      X' ≤ Real.exp (σ*L) → X' ≤ Kx*Real.exp L → X ≤ 2*X' → X' ≤ 2*X →
      ∀ {J J' : Type} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
      (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J' cfg L X'),
      z'.Y=z.Y → ∀ theta : ℝ, |theta| ≤ cfg.Kθ*L^cfg.A₀ →
      ‖z.comparableSource z' cutoff ψ theta‖ ≤ (z.Y*X)*L^(-P) := by
  filter_upwards [markedMajorMellinLabelEnergy_comparable_all_log cfg σ Kx hσ cutoff hcutoff hnorm
    hlo hhi hsupp ψ (half_pos hlo) hinterval hψ (P+1) (by linarith),
    eventually_ge_atTop (4:ℝ)] with L hL hL4
  intro X X' hX1 hX'1 hupper hcomp hupper' hcomp' hlow hupp J J' _ _ _ _ z z' hY theta htheta
  have hX : 0 < X := by linarith
  have hX' : 0 < X' := by linarith
  have hLp : 0 < L := by linarith
  have H := markedMajorLabel_comparable_full_source_energy z.allBands z'.allBands z.allBands_prime z'.allBands_prime
    cutoff hlo hinterval hsupp z.χb z'.χb z.χ z'.χ z.θ z'.θ theta z.Y
    (Real.exp (L^(6/25:ℝ))) X X' z.H z.u z.v z.U z'.H z'.u z'.v z'.U z.modulation z'.modulation
    z.l z.r z'.l z'.r z.β z'.β z.Y_pos hX hX' z.H_pos z.U_pos z'.H_pos z'.U_pos
    z.product_eq z'.product_eq hlow hupp z.H_le_u z.u_le_v z.v_le_two_H z.U_le_l z.r_le_two_U
    z'.H_le_u z'.u_le_v z'.v_le_two_H z'.U_le_l z'.r_le_two_U ψ hψ
  have he := hL X X' hX1 hX'1 hX hupper hcomp hupper' hcomp' hlow z z' theta htheta
  have hbound := mul_le_mul_of_nonneg_left he (show 0 ≤ 4*z.Y*X by have := z.Y_pos; positivity)
  simp only [MarkedMajorLabelEnergyData.endpoint,MarkedMajorLabelEnergyData.conjugateEndpoint,hY] at hbound
  have H' := H.trans hbound
  have hraw : ‖z.comparableSource z' cutoff ψ theta‖ ≤ (4*z.Y*X)*L^(-(P+1)) := by
    simpa only [MarkedMajorLabelEnergyData.comparableSource,hY,
      markedMajor_source_difference hX.ne' z.Y_pos.ne'] using H'
  have hlog : 4*L^(-(P+1)) ≤ L^(-P) := by
    calc
      _ ≤ L*L^(-(P+1)) := mul_le_mul_of_nonneg_right hL4 (Real.rpow_nonneg hLp.le _)
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one L]
        rw [← Real.rpow_add hLp]
        congr 1
        ring
  calc
    _ ≤ (4*z.Y*X)*L^(-(P+1)) := hraw
    _ = (z.Y*X)*(4*L^(-(P+1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (mul_pos z.Y_pos hX).le

end
end ArtinMatthews
