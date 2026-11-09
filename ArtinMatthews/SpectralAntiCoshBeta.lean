module

public import ArtinMatthews.SpectralExpUnitSubstitution


set_option backward.privateInPublic true
@[expose] public section

/-! The beta value of the singular cosh-minus-one profile.  Its open
half-line excludes the single zero of cosh(u)-1; the natural beta conditions
will enforce integrability at that endpoint. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

def spectralAntiCoshBetaProfile (s ν : ℂ) (u : ℝ) : ℂ :=
  ((Real.cosh u-1 : ℝ) : ℂ)^(-s)*Complex.exp (ν*(u : ℂ))

theorem spectral_cosh_sub_one_exp {u : ℝ} (_hu : 0 < u) :
    Real.cosh u-1 = ((1-Real.exp (-u))*(1-Real.exp (-u)))/(2*Real.exp (-u)) := by
  have h : Real.exp (-u) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.cosh_eq,show Real.exp u = (Real.exp (-u))⁻¹ by rw [Real.exp_neg,inv_inv]]
  field_simp [h]
  ring

theorem spectralAntiCoshBetaProfile_eq (s ν : ℂ) {u : ℝ} (hu : 0 < u) :
    spectralAntiCoshBetaProfile s ν u = (2 : ℂ)^s*
      ((Real.exp (-u) : ℂ)*spectralUnitBetaProfile (s-ν) (1-2*s) (Real.exp (-u))) := by
  let v := Real.exp (-u)
  have hv : 0 < v := Real.exp_pos _
  have hv1 : v < 1 := by dsimp [v]; simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos hu)
  have hw : 0 < 1-v := sub_pos.mpr hv1
  have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hpow : ((Real.cosh u-1 : ℝ) : ℂ)^(-s) =
      (2 : ℂ)^s*(v : ℂ)^s*((1-(v : ℂ))^(-s)*(1-(v : ℂ))^(-s)) := by
    rw [spectral_cosh_sub_one_exp hu]
    change (((1-v)*(1-v)/(2*v) : ℝ) : ℂ)^(-s) = _
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg
      (mul_nonneg hw.le hw.le) (mul_nonneg zero_le_two hv.le)]
    have hn := Complex.mul_cpow_ofReal_nonneg hw.le hw.le (-s)
    have hd := Complex.mul_cpow_ofReal_nonneg zero_le_two hv.le (-s)
    rw [← Complex.ofReal_mul] at hn hd
    rw [hn,hd]
    simp only [Complex.cpow_neg,div_eq_mul_inv,mul_inv,inv_inv]
    push_cast
    ring
  have hexp : Complex.exp (ν*(u : ℂ)) = (v : ℂ)^(-ν) := by
    rw [Complex.cpow_def_of_ne_zero hvc,← Complex.ofReal_log hv.le]
    dsimp [v]
    rw [Real.log_exp]
    congr 1
    push_cast
    ring
  have hvpower : (v : ℂ)*(v : ℂ)^(s-ν-1) = (v : ℂ)^(s-ν) := by
    nth_rw 1 [← Complex.cpow_one (v : ℂ)]
    rw [← Complex.cpow_add _ _ hvc]
    congr 1
    ring
  have hphase : (v : ℂ)^s*(v : ℂ)^(-ν) = (v : ℂ)^(s-ν) := by
    rw [← Complex.cpow_add _ _ hvc]
    congr 1
  have hweight : (1-(v : ℂ))^(-s)*(1-(v : ℂ))^(-s) =
      (1-(v : ℂ))^((1-2*s)-1) := by
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hw.ne')]
    congr 1
    ring
  unfold spectralAntiCoshBetaProfile spectralUnitBetaProfile
  rw [hpow,hexp]
  change _ = (2 : ℂ)^s*((v : ℂ)*((v : ℂ)^(s-ν-1)*(1-(v : ℂ))^((1-2*s)-1)))
  rw [← mul_assoc (v : ℂ),hvpower,← hweight]
  calc
    _ = (2 : ℂ)^s*((v : ℂ)^s*(v : ℂ)^(-ν))*
        ((1-(v : ℂ))^(-s)*(1-(v : ℂ))^(-s)) := by ring
    _ = _ := by rw [hphase]; ring

theorem spectralAntiCoshBetaProfile_integrable (s ν : ℂ)
    (hleft : ν.re < s.re) (hright : s.re < 1/2) :
    IntegrableOn (spectralAntiCoshBetaProfile s ν) (Ioi (0 : ℝ)) := by
  have ha : 0 < (s-ν).re := by simpa using sub_pos.mpr hleft
  have hb : 0 < (1-2*s).re := by norm_num; linarith
  have hi := (spectralExpNeg_integrable (spectralUnitBetaProfile (s-ν) (1-2*s))).mp
    (spectralUnitBetaProfile_integrable _ _ ha hb)
  apply (hi.const_mul ((2 : ℂ)^s)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (spectralAntiCoshBetaProfile_eq s ν hu).symm

theorem spectralAntiCoshBetaProfile_integral (s ν : ℂ) :
    (∫ u in Ioi (0 : ℝ), spectralAntiCoshBetaProfile s ν u) =
      (2 : ℂ)^s*Complex.betaIntegral (s-ν) (1-2*s) := by
  calc
    _ = (2 : ℂ)^s*∫ u in Ioi (0 : ℝ),
        (Real.exp (-u) : ℂ)*spectralUnitBetaProfile (s-ν) (1-2*s) (Real.exp (-u)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact spectralAntiCoshBetaProfile_eq s ν hu
    _ = _ := by rw [← spectralExpNeg_integral,spectralUnitBetaProfile_integral]

end ArtinMatthews
