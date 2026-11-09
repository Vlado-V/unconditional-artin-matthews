module

public import ArtinMatthews.MarkedMajorMellinIsolationBound


set_option backward.privateInPublic true
@[expose] public section

/-! Exact absolutely convergent Mellin isolation for positive compact cutoffs. -/
namespace ArtinMatthews
open MeasureTheory Set Complex
open scoped ContDiff FourierTransform SchwartzMap
noncomputable section

theorem markedMellinIsolation_phase_integrable
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Icc a b) (θ z : ℝ) :
    Integrable (fun ξ : ℝ => markedMellinIsolationCoefficient η hη ha hsupp θ ξ *
      Complex.exp (I*(ξ:ℂ)*(z:ℂ))) := by
  apply (markedMellinIsolationCoefficient η hη ha hsupp θ).integrable.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · apply Filter.Eventually.of_forall
    intro ξ
    have he : I*(ξ:ℂ)*(z:ℂ) = ((ξ*z:ℝ):ℂ)*I := by push_cast; ring
    rw [he,Complex.norm_exp_ofReal_mul_I]

theorem markedMellinIsolation_log_inversion
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Icc a b) (θ z : ℝ) :
    markedMellinIsolationLogProfile η θ z =
      ∫ ξ : ℝ, markedMellinIsolationCoefficient η hη ha hsupp θ ξ *
        Complex.exp (I*(ξ:ℂ)*(z:ℂ)) := by
  let g := markedMellinIsolationSchwartz η hη ha hsupp θ
  let c : ℝ := 2*Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  let H : ℝ → ℂ := fun v => (𝓕 g) v * Complex.exp (I*((c*v:ℝ):ℂ)*(z:ℂ))
  have hbase : markedMellinIsolationLogProfile η θ z = ∫ v : ℝ, H v := by
    have h := congrFun (g.continuous.fourierInv_fourier_eq g.integrable (𝓕 g).integrable) z
    rw [Real.fourierInv_eq'] at h
    change (∫ v : ℝ, Complex.exp (((2*Real.pi*inner ℝ v z : ℝ):ℂ)*I) • (𝓕 g) v) =
      markedMellinIsolationLogProfile η θ z at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards with v
    dsimp [H,c]
    change Complex.exp (((2*Real.pi*(z*v):ℝ):ℂ)*I) * (𝓕 g) v = _
    have he : (((2*Real.pi*(z*v):ℝ):ℂ)*I) = I*((2*Real.pi*v:ℝ):ℂ)*(z:ℂ) := by
      push_cast
      ring
    rw [he,mul_comm]
  have hp (ξ : ℝ) : markedMellinIsolationCoefficient η hη ha hsupp θ ξ *
      Complex.exp (I*(ξ:ℂ)*(z:ℂ)) = c⁻¹ • H (ξ/c) := by
    rw [markedMellinIsolationCoefficient_apply]
    dsimp [H]
    rw [mul_div_cancel₀ _ hc.ne']
    change ((c⁻¹:ℝ):ℂ) * (𝓕 g) (ξ/c) * _ = _
    ring
  rw [show (fun ξ : ℝ => markedMellinIsolationCoefficient η hη ha hsupp θ ξ *
      Complex.exp (I*(ξ:ℂ)*(z:ℂ))) = (fun ξ => c⁻¹ • H (ξ/c)) from funext hp]
  rw [integral_smul,Measure.integral_comp_div H c,abs_of_pos hc,
    smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
  exact hbase

theorem markedMellinIsolation_inversion
    (η : ℝ → ℂ) (hη : ContDiff ℝ ∞ η) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support η ⊆ Icc a b) (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    η y * Complex.exp (-(2*(Real.pi:ℂ)*I*(θ:ℂ)*(y:ℂ))) =
      ∫ ξ : ℝ, markedMellinIsolationCoefficient η hη ha hsupp θ ξ *
        Complex.exp (I*(ξ:ℂ)*(Real.log y:ℂ)) := by
  have h := markedMellinIsolation_log_inversion η hη ha hsupp θ (Real.log y)
  rw [markedMellinIsolationLogProfile_eq,Real.exp_log hy,
    markedMellinIsolatedCutoff_eq] at h
  exact h

end
end ArtinMatthews
