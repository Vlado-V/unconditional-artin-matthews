module

public import ArtinMatthews.SpectralGamma0FormOperator


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine coercive rotation off the nonnegative real spectral ray. -/
noncomputable section
namespace ArtinMatthews

def spectralResolventRotation (z : ℂ) : ℂ := 1-star z/(‖z‖:ℂ)

def spectralResolventCoercivity (z : ℂ) : ℝ :=
  min (1-z.re/‖z‖) (‖z‖-z.re)

theorem spectralResolvent_norm_pos (z : ℂ) (hz : z.re < ‖z‖) : 0 < ‖z‖ := by
  apply norm_pos_iff.mpr
  intro h
  simp only [h,Complex.zero_re,norm_zero,lt_self_iff_false] at hz

theorem spectralResolventRotation_re (z : ℂ) :
    (spectralResolventRotation z).re=1-z.re/‖z‖ := by
  simp [spectralResolventRotation,Complex.div_ofReal_re]

theorem spectralResolventRotation_re_pos (z : ℂ) (hz : z.re < ‖z‖) :
    0 < (spectralResolventRotation z).re := by
  rw [spectralResolventRotation_re]
  have hd : z.re/‖z‖ < 1 := (div_lt_one (spectralResolvent_norm_pos z hz)).mpr hz
  linarith

theorem spectralResolventRotation_ne_zero (z : ℂ) (hz : z.re < ‖z‖) :
    spectralResolventRotation z ≠ 0 := by
  intro h
  have hp := spectralResolventRotation_re_pos z hz
  simp only [h,Complex.zero_re,lt_self_iff_false] at hp

theorem spectralResolventCoercivity_pos (z : ℂ) (hz : z.re < ‖z‖) :
    0 < spectralResolventCoercivity z := by
  apply lt_min
  · exact spectralResolventRotation_re z ▸ spectralResolventRotation_re_pos z hz
  · exact sub_pos.mpr hz

theorem spectralResolventRotation_mul (z : ℂ) (hz : z.re < ‖z‖) :
    spectralResolventRotation z*z=z-(‖z‖:ℂ) := by
  have hn : (‖z‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (spectralResolvent_norm_pos z hz).ne'
  unfold spectralResolventRotation
  have hc : star z*z=(Complex.normSq z:ℂ) := by
    change (starRingEnd ℂ) z*z=(Complex.normSq z:ℂ)
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [sub_mul,one_mul,div_mul_eq_mul_div,hc,Complex.normSq_eq_norm_sq]
  congr 1
  push_cast
  field_simp

theorem spectralResolventRotation_energy (z : ℂ) (hz : z.re < ‖z‖) (g m : ℝ) :
    (spectralResolventRotation z*((g:ℂ)-z*(m:ℂ))).re=
      (1-z.re/‖z‖)*g+(‖z‖-z.re)*m := by
  have he : spectralResolventRotation z*((g:ℂ)-z*(m:ℂ))=
      spectralResolventRotation z*(g:ℂ)-(z-(‖z‖:ℂ))*(m:ℂ) := by
    rw [mul_sub,← mul_assoc,spectralResolventRotation_mul z hz]
  rw [he]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,
    sub_zero,spectralResolventRotation_re]
  ring

end ArtinMatthews
