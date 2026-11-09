module

public import ArtinMatthews.SpectralEisensteinRadialDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! A single positive radial envelope controls every compact approximant
and its hyperbolic derivative. Its difference from the actual remainder
profile is a genuine compact smooth profile. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

def eisensteinRadialEnvelope (σ h : ℝ) : ℝ :=
  (1-eisensteinHeightCutoff (h/2))*h^σ

def eisensteinEnvelopeCorrection (s : ℂ) (h : ℝ) : ℂ :=
  ((eisensteinHeightCutoff h-eisensteinHeightCutoff (h/2):ℝ):ℂ)*(h:ℂ)^s

theorem eisensteinEnvelopeCorrection_zero_low (s : ℂ) {h : ℝ} (hh : h ≤ 1) :
    eisensteinEnvelopeCorrection s h=0 := by
  rw [eisensteinEnvelopeCorrection,eisensteinHeightCutoff_zero hh,
    eisensteinHeightCutoff_zero (by linarith : h/2 ≤ 1)]
  simp

theorem eisensteinEnvelopeCorrection_zero_high (s : ℂ) {h : ℝ} (hh : 4 ≤ h) :
    eisensteinEnvelopeCorrection s h=0 := by
  rw [eisensteinEnvelopeCorrection,eisensteinHeightCutoff_one (by linarith : 2 ≤ h),
    eisensteinHeightCutoff_one (by linarith : 2 ≤ h/2)]
  simp

theorem eisensteinEnvelopeCorrection_smooth (s : ℂ) :
    ContDiff ℝ ∞ (eisensteinEnvelopeCorrection s) := by
  rw [contDiff_iff_contDiffAt]
  intro h
  by_cases hh : 0 < h
  · have hlog : ContDiffAt ℝ ∞ (fun t : ℝ => (Real.log t:ℂ)) h :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp h (Real.contDiffAt_log.mpr hh.ne')
    have hp : ContDiffAt ℝ ∞ (fun t : ℝ => (t:ℂ)^s) h := by
      have he : (fun t : ℝ => (t:ℂ)^s)=ᶠ[𝓝 h]
          (fun t : ℝ => Complex.exp (s*(Real.log t:ℂ))) := by
        filter_upwards [eventually_gt_nhds hh] with t ht
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
          ← Complex.ofReal_log ht.le,mul_comm]
      exact ((contDiffAt_const.mul hlog).cexp).congr_of_eventuallyEq he
    have hc : ContDiff ℝ ∞ (fun t : ℝ => eisensteinHeightCutoff t-eisensteinHeightCutoff (t/2)) :=
      eisensteinHeightCutoff_contDiff.sub
        (eisensteinHeightCutoff_contDiff.comp (contDiff_id.div_const 2))
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp h hc.contDiffAt).mul hp
  · have he : eisensteinEnvelopeCorrection s =ᶠ[𝓝 h] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds (show h < 1 by linarith)] with t ht
      exact eisensteinEnvelopeCorrection_zero_low s ht.le
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem eisensteinEnvelopeCorrection_support (s : ℂ) :
    tsupport (eisensteinEnvelopeCorrection s) ⊆ Icc (1:ℝ) 4 := by
  apply closure_minimal _ isClosed_Icc
  intro h hh
  by_contra hn
  have ho : h < 1 ∨ 4 < h := by simpa only [mem_Icc,not_and_or,not_le] using hn
  rcases ho with ho | ho
  · exact hh (eisensteinEnvelopeCorrection_zero_low s ho.le)
  · exact hh (eisensteinEnvelopeCorrection_zero_high s ho.le)

theorem eisensteinEnvelopeCorrection_compact (s : ℂ) :
    HasCompactSupport (eisensteinEnvelopeCorrection s) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (eisensteinEnvelopeCorrection_support s)

theorem eisensteinEnvelopeCorrection_positive_support (s : ℂ) :
    tsupport (eisensteinEnvelopeCorrection s) ⊆ Ioi (0:ℝ) :=
  fun _ h => lt_of_lt_of_le (by norm_num) (eisensteinEnvelopeCorrection_support s h).1

theorem eisensteinRadialEnvelope_nonneg (σ : ℝ) {h : ℝ} (hh : 0 < h) :
    0 ≤ eisensteinRadialEnvelope σ h :=
  mul_nonneg (sub_nonneg.mpr (eisensteinHeightCutoff_range _).2) (Real.rpow_nonneg hh.le _)

theorem eisensteinRadialEnvelope_decomposition (σ : ℝ) {h : ℝ} (hh : 0 < h) :
    (eisensteinRadialEnvelope σ h:ℂ)=
      eisensteinRemainderProfile (σ:ℂ) h+eisensteinEnvelopeCorrection (σ:ℂ) h := by
  rw [eisensteinRadialEnvelope,eisensteinRemainderProfile,eisensteinEnvelopeCorrection,
    Complex.ofReal_mul,← Complex.ofReal_cpow hh.le]
  push_cast
  ring

theorem eisensteinRadialApprox_norm_envelope (s : ℂ) (A : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖eisensteinRadialApprox s A h‖ ≤ eisensteinRadialEnvelope s.re h := by
  by_cases h2 : h ≤ 2
  · rw [eisensteinRadialEnvelope,eisensteinHeightCutoff_zero (by linarith : h/2 ≤ 1)]
    simpa only [sub_zero,one_mul] using eisensteinRadialApprox_norm_le s A h hh
  · rw [eisensteinRadialApprox_large_zero s A (not_le.mp h2).le,norm_zero]
    exact eisensteinRadialEnvelope_nonneg s.re hh

theorem eisensteinRadialApprox_deriv_envelope (s : ℂ) (A M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, |t*deriv eisensteinHeightCutoff t| ≤ M) {h : ℝ} (hh : 0 < h) :
    ‖(h:ℂ)*deriv (eisensteinRadialApprox s A) h‖ ≤
      (2*M+‖s‖)*eisensteinRadialEnvelope s.re h := by
  by_cases h2 : h ≤ 2
  · rw [eisensteinRadialEnvelope,eisensteinHeightCutoff_zero (by linarith : h/2 ≤ 1)]
    simpa only [sub_zero,one_mul] using eisensteinRadialApprox_weighted_deriv_le s A h M hM hbound hh
  · have he : eisensteinRadialApprox s A =ᶠ[𝓝 h] fun _ => 0 := by
      filter_upwards [eventually_gt_nhds (not_le.mp h2)] with t ht
      exact eisensteinRadialApprox_large_zero s A ht.le
    rw [he.deriv_eq,deriv_const,mul_zero,norm_zero]
    exact mul_nonneg (by positivity) (eisensteinRadialEnvelope_nonneg s.re hh)

end ArtinMatthews
