module

public import ArtinMatthews.SpectralEisensteinCutoffAtCusps
public import ArtinMatthews.SpectralFourierBruhatKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact compatibility of the completed common-period horizontal mean
with the actual determinant-one true-width cusp scaling. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspPeriodic_normalized_dilation_mean (F : ℝ → ℂ) (hF : Continuous F)
    (hp : Function.Periodic F 1) (w L : ℝ) (hw : 0<w) (hL : 0<L)
    (d : ℕ) (hLd : L=w*(d:ℝ)) :
    (L:ℂ)⁻¹*(∫ x in (0:ℝ)..L, F (x/w))=∫ x in (0:ℝ)..1, F x := by
  have hdiv : L/w=(d:ℝ) := by rw [hLd];field_simp
  have hi : (∫ x in (0:ℝ)..(d:ℝ), F x)=(d:ℂ)*(∫ x in (0:ℝ)..1, F x) := by
    have h := hp.intervalIntegral_add_zsmul_eq (d:ℤ) 0 (fun a b => hF.intervalIntegrable a b)
    simpa only [zero_add,zsmul_eq_mul,Int.cast_natCast,mul_one] using h
  rw [intervalIntegral.integral_comp_div _ hw.ne',zero_div,hdiv,hi]
  simp only [Complex.real_smul]
  have hLc : (L:ℂ)=(w:ℂ)*(d:ℂ) := by exact_mod_cast hLd
  have hLn : (L:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL.ne'
  field_simp
  rw [hLc]

theorem gamma0Invariant_trueCusp_horocycle_periodic (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (F : UpperHalfPlane → ℂ)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ.val • z)=F z)
    (y : ℝ) (hy : 0<y) :
    Function.Periodic (fun x => F (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)) 1 := by
  intro x
  obtain ⟨γ,hγ⟩ := gamma0TrueCuspScaling_integer_period N r 1
  have hp : gamma0EisensteinHorizontalPoint y hy (x+1)=
      realTranslation 1 • gamma0EisensteinHorizontalPoint y hy x := by
    apply UpperHalfPlane.ext
    rw [realTranslation_coe_smul]
    apply Complex.ext <;> simp [gamma0EisensteinHorizontalPoint]
  have hm : gamma0TrueCuspScaling N r*realTranslation 1=
      atkinRealMap γ.val*gamma0TrueCuspScaling N r := by
    norm_num only [Int.cast_one] at hγ
    rw [hγ]
    group
  change F (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy (x+1))=
    F (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)
  rw [hp,← mul_smul,hm,mul_smul,atkinRealMap_smul]
  exact hF γ _

theorem gamma0TrueCuspScaling_horizontal_dilation (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (t : ℝ) (ht : 0<t) (x : ℝ) :
    gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint
      (t/(gamma0CuspTrueWidth N r:ℝ))
      (div_pos ht (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)))
      (x/(gamma0CuspTrueWidth N r:ℝ))=
      r⁻¹ • gamma0EisensteinHorizontalPoint t ht x := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0<w := by dsimp [w];exact_mod_cast gamma0CuspTrueWidth_pos N r
  have hp : cuspWidthDilation w hw • gamma0EisensteinHorizontalPoint (t/w) (div_pos ht hw) (x/w)=
      gamma0EisensteinHorizontalPoint t ht x := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (cuspWidthDilation w hw • gamma0EisensteinHorizontalPoint (t/w) _ (x/w)).re=x
      rw [cuspWidthDilation_re_smul]
      change w*(x/w)=x
      field_simp
    · change (cuspWidthDilation w hw • gamma0EisensteinHorizontalPoint (t/w) _ (x/w)).im=t
      rw [cuspWidthDilation_im_smul]
      change w*(t/w)=t
      field_simp
  rw [gamma0TrueCuspScaling,mul_smul,hp,← map_inv,atkinRealMap_smul]

theorem gamma0Invariant_common_mean_trueWidth (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (F : UpperHalfPlane → ℂ) (hc : Continuous F)
    (hF : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ.val • z)=F z)
    (t : ℝ) (ht : 0<t) :
    (N:ℂ)⁻¹*(∫ x in (0:ℝ)..(N:ℝ), F (r⁻¹ • gamma0EisensteinHorizontalPoint t ht x))=
      ∫ x in (0:ℝ)..1, F (gamma0TrueCuspScaling N r •
        gamma0EisensteinHorizontalPoint (t/(gamma0CuspTrueWidth N r:ℝ))
          (div_pos ht (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r))) x) := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0<w := by dsimp [w];exact_mod_cast gamma0CuspTrueWidth_pos N r
  let G := fun x => F (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint (t/w) (div_pos ht hw) x)
  have hG : Continuous G := hc.comp ((continuous_const_smul _).comp
    (gamma0EisensteinHorizontalPoint_continuous (t/w) (div_pos ht hw)))
  have hp := gamma0Invariant_trueCusp_horocycle_periodic N r F hF (t/w) (div_pos ht hw)
  have he : (fun x => F (r⁻¹ • gamma0EisensteinHorizontalPoint t ht x))=(fun x => G (x/w)) := by
    funext x
    rw [← gamma0TrueCuspScaling_horizontal_dilation N r t ht x]
  rw [he]
  apply cuspPeriodic_normalized_dilation_mean G hG hp w (N:ℝ) hw (Nat.cast_pos.mpr (NeZero.pos N))
    (gamma0CuspFrequencyStep N r)
  dsimp [w]
  exact_mod_cast (gamma0CuspFrequencyStep_mul_width N r).symm

end ArtinMatthews
