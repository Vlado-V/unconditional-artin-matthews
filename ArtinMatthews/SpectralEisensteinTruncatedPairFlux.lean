module

public import ArtinMatthews.SpectralEisensteinCriticalPowerFlux
public import ArtinMatthews.SpectralEisensteinOutgoingDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! Exact upper-band imaginary flux of a compact incoming and outgoing
pair. At the lower endpoint the cutoff and its derivative have the
untruncated data, while the pair vanishes at the upper endpoint. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff InnerProductSpace
namespace ArtinMatthews

def eisensteinCriticalTruncatedPair (s : ℂ) (A : ℝ) (a b : ℂ) (t : ℝ) : ℂ :=
  a*eisensteinOutgoingApprox s A t+b*eisensteinOutgoingApprox (1-s) A t

def eisensteinCriticalUpperErrorPair (s : ℂ) (A : ℝ) (a b : ℂ) (t : ℝ) : ℂ :=
  a*eisensteinUpperCutoffError s A t+b*eisensteinUpperCutoffError (1-s) A t

theorem spectralDeriv_linearCombination (f g : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (a b : ℂ) (t : ℝ) :
    deriv (fun u => a*f u+b*g u) t=a*deriv f t+b*deriv g t :=
  (((hf t).hasDerivAt.const_mul a).add ((hg t).hasDerivAt.const_mul b)).deriv

theorem spectralSecondDeriv_linearCombination (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (a b : ℂ) (t : ℝ) :
    deriv (deriv (fun u => a*f u+b*g u)) t=
      a*deriv (deriv f) t+b*deriv (deriv g) t := by
  rw [funext (spectralDeriv_linearCombination f g (hf.differentiable (by simp)) (hg.differentiable (by simp)) a b)]
  exact spectralDeriv_linearCombination (deriv f) (deriv g)
    ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp))
    ((contDiff_infty_iff_deriv.mp hg).2.differentiable (by simp)) a b t

theorem eisensteinCriticalTruncatedPair_smooth (s : ℂ) (A : ℝ) (a b : ℂ) :
    ContDiff ℝ ∞ (eisensteinCriticalTruncatedPair s A a b) :=
  (contDiff_const.mul (eisensteinOutgoingApprox_smooth s A)).add
    (contDiff_const.mul (eisensteinOutgoingApprox_smooth (1-s) A))

theorem eisensteinCriticalUpperErrorPair_smooth (s : ℂ) (A : ℝ) (a b : ℂ) :
    ContDiff ℝ ∞ (eisensteinCriticalUpperErrorPair s A a b) :=
  (contDiff_const.mul (eisensteinUpperCutoffError_smooth s A)).add
    (contDiff_const.mul (eisensteinUpperCutoffError_smooth (1-s) A))

theorem eisensteinCriticalTruncatedPair_high_error (s : ℂ) {A : ℝ} (hA : 0<A) (hA2 : A≤1/2)
    (a b : ℂ) {t : ℝ} (ht : 2<t) :
    spectralRadialError (s*(1-s)) (eisensteinCriticalTruncatedPair s A a b) t=
      -eisensteinCriticalUpperErrorPair s A a b t := by
  have hs := eisensteinOutgoingApprox_radial_error s hA hA2 t
  have hq := eisensteinOutgoingApprox_radial_error (1-s) hA hA2 t
  rw [eisensteinVerticalCutoffError_zero s (Or.inr ht),zero_sub] at hs
  rw [show (1-s)*(1-(1-s))=s*(1-s) by ring,
    eisensteinVerticalCutoffError_zero (1-s) (Or.inr ht),zero_sub] at hq
  have hd : deriv (deriv (eisensteinCriticalTruncatedPair s A a b)) t =
      a*deriv (deriv (eisensteinOutgoingApprox s A)) t+
        b*deriv (deriv (eisensteinOutgoingApprox (1-s) A)) t :=
    spectralSecondDeriv_linearCombination _ _ (eisensteinOutgoingApprox_smooth s A)
      (eisensteinOutgoingApprox_smooth (1-s) A) a b t
  rw [spectralRadialError,hd]
  unfold eisensteinCriticalTruncatedPair eisensteinCriticalUpperErrorPair
  linear_combination a*hs+b*hq

theorem eisensteinOutgoingApprox_lower_edge (q : ℂ) {A : ℝ} (hA : 0<A) (hA2 : A<1/2) :
    eisensteinOutgoingApprox q A (1/A)=((1/A:ℝ):ℂ)^q ∧
      deriv (eisensteinOutgoingApprox q A) (1/A)=q*((1/A:ℝ):ℂ)^(q-1) := by
  have hL : 0<1/A := one_div_pos.mpr hA
  have hL2 : 2<1/A := (lt_div_iff₀ hA).mpr (by linarith)
  have hAL : A*(1/A)=1 := by field_simp
  have hc : eisensteinHeightCutoff (A*(1/A))=0 :=
    eisensteinHeightCutoff_zero (le_of_eq hAL)
  have hd : deriv eisensteinHeightCutoff (A*(1/A))=0 :=
    spectral_deriv_zero_on_left (eisensteinHeightCutoff_contDiff.continuous_deriv (by simp))
      1 (fun _ ht => eisensteinHeightCutoff_zero ht) _ (le_of_eq hAL)
  constructor
  · rw [eisensteinOutgoingApprox,eisensteinHeightCutoff_one hL2.le,hc]
    simp
  · rw [eisensteinOutgoingApprox_deriv q A (1/A) hL,eisensteinHeightCutoff_one hL2.le,hc,hd,
      eisensteinHeightCutoff_deriv_zero (Or.inr hL2)]
    simp

theorem eisensteinCriticalTruncatedPair_lower_flux {s : ℂ} (hs : s.re=1/2)
    {A : ℝ} (hA : 0<A) (hA2 : A<1/2) (a b : ℂ) :
    spectralRadialFlux (eisensteinCriticalTruncatedPair s A a b) (1/A)=
      s.im*(‖a‖^2-‖b‖^2) := by
  have hd : deriv (eisensteinCriticalTruncatedPair s A a b) (1/A)=
      a*deriv (eisensteinOutgoingApprox s A) (1/A)+b*deriv (eisensteinOutgoingApprox (1-s) A) (1/A) :=
    spectralDeriv_linearCombination _ _ ((eisensteinOutgoingApprox_smooth s A).differentiable (by simp))
      ((eisensteinOutgoingApprox_smooth (1-s) A).differentiable (by simp)) a b (1/A)
  rw [spectralRadialFlux,hd,eisensteinCriticalTruncatedPair,
    (eisensteinOutgoingApprox_lower_edge s hA hA2).1,(eisensteinOutgoingApprox_lower_edge (1-s) hA hA2).1,
    (eisensteinOutgoingApprox_lower_edge s hA hA2).2,(eisensteinOutgoingApprox_lower_edge (1-s) hA hA2).2]
  exact eisensteinCriticalPower_pair_flux hs (one_div_pos.mpr hA) a b

theorem eisensteinCriticalTruncatedPair_upper_flux (s : ℂ) {A : ℝ} (hA : 0<A) (a b : ℂ) :
    spectralRadialFlux (eisensteinCriticalTruncatedPair s A a b) (2/A)=0 := by
  have h0 : eisensteinCriticalTruncatedPair s A a b (2/A)=0 := by
    simp only [eisensteinCriticalTruncatedPair,eisensteinOutgoingApprox_zero_high s hA le_rfl,
      eisensteinOutgoingApprox_zero_high (1-s) hA le_rfl,mul_zero,add_zero]
  rw [spectralRadialFlux,h0,inner_zero_left,Complex.zero_im]

theorem eisensteinCriticalTruncatedPair_upper_band_flux {s : ℂ} (hs : s.re=1/2)
    {A : ℝ} (hA : 0<A) (hA2 : A<1/2) (a b : ℂ) :
    (∫ t in (1/A)..(2/A), ((t^2:ℝ)⁻¹) •
      inner ℂ (eisensteinCriticalUpperErrorPair s A a b t) (eisensteinCriticalTruncatedPair s A a b t)).im=
      s.im*(‖a‖^2-‖b‖^2) := by
  let f := eisensteinCriticalTruncatedPair s A a b
  let g := eisensteinCriticalUpperErrorPair s A a b
  let L : ℝ := 1/A
  let U : ℝ := 2/A
  have hL : 0<L := one_div_pos.mpr hA
  have hL2 : 2<L := (lt_div_iff₀ hA).mpr (by linarith)
  have hLU : L≤U := div_le_div_of_nonneg_right (by norm_num) hA.le
  have hEq : (∫ t in L..U, ((t^2:ℝ)⁻¹) • inner ℂ (f t)
      (spectralRadialError (s*(1-s)) f t)) =
      ∫ t in L..U, -((starRingEnd ℂ) (((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htL : L≤t := (uIcc_of_le hLU ▸ ht).1
    have hRad : spectralRadialError (s*(1-s)) f t=-g t :=
      eisensteinCriticalTruncatedPair_high_error s hA hA2.le a b (hL2.trans_le htL)
    change ((t^2:ℝ)⁻¹) • inner ℂ (f t) (spectralRadialError (s*(1-s)) f t)=
      -((starRingEnd ℂ) (((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t)))
    rw [hRad,inner_neg_right,smul_neg,Complex.real_smul,Complex.real_smul,map_mul,Complex.conj_ofReal,
      inner_conj_symm]
  have hstar : (∫ t in L..U, (starRingEnd ℂ) (((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t))) =
      (starRingEnd ℂ) (∫ t in L..U, ((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t)) :=
    Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm
      (fun t => ((t^2:ℝ)⁻¹) • inner ℂ (g t) (f t))
  have hf := spectralRadialError_im_integral (s*(1-s)) (eisensteinCriticalParameter_real hs)
    f (eisensteinCriticalTruncatedPair_smooth s A a b) hL hLU
  rw [hEq,intervalIntegral.integral_neg,hstar,Complex.neg_im,Complex.conj_im,neg_neg,
    eisensteinCriticalTruncatedPair_lower_flux hs hA hA2 a b,
    eisensteinCriticalTruncatedPair_upper_flux s hA a b,sub_zero] at hf
  exact hf

end ArtinMatthews
