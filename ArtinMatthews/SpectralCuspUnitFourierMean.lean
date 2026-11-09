module

public import ArtinMatthews.SpectralEisensteinPrimitiveHorocycles
public import ArtinMatthews.SpectralCuspWidthNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The exact unit-period Fourier coefficient of a continuous section.
A common-period mode divisible by the cusp frequency step gives the same
normalized mean as its corresponding true-width mode. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

def gamma0UnitCuspFourierMean (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (m : ℤ)
    (F : UpperHalfPlane → ℂ) (y : ℝ) : ℂ :=
  if hy : 0 < y then
    ∫ x in (0 : ℝ)..1, cuspFourierPhase 1 m x *
      F (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x)
  else 0

theorem gamma0TrueCuspScaling_horizontalPoint (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    let w : ℝ := gamma0CuspTrueWidth N r
    let hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
    gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint y hy x =
      r⁻¹ • gamma0EisensteinHorizontalPoint (w*y) (mul_pos hw hy) (w*x) := by
  dsimp only
  rw [gamma0TrueCuspScaling,mul_smul,← map_inv,atkinRealMap_smul]
  congr 1
  apply UpperHalfPlane.ext
  rw [cuspWidthDilation_coe_smul]
  apply Complex.ext
  · simp [gamma0EisensteinHorizontalPoint]
  · simp [gamma0EisensteinHorizontalPoint]

theorem gamma0CuspCommonPhase_trueWidth_periodic (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (m : ℤ) :
    Function.Periodic
      (cuspFourierPhase (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*m))
      (gamma0CuspTrueWidth N r : ℝ) := by
  let w : ℝ := gamma0CuspTrueWidth N r
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  intro x
  change cuspFourierPhase (N : ℝ) _ (x+w) = cuspFourierPhase (N : ℝ) _ x
  calc
    _ = cuspFourierPhase (N : ℝ) _ (w*(x/w+1)) := by
      congr 1
      field_simp [hw.ne']
    _ = cuspFourierPhase 1 m (x/w+1) := cuspFourierPhase_trueWidth N r m _
    _ = cuspFourierPhase 1 m (x/w) := cuspFourierPhase_periodic 1 one_pos m _
    _ = cuspFourierPhase (N : ℝ) _ (w*(x/w)) := (cuspFourierPhase_trueWidth N r m _).symm
    _ = _ := by congr 1; field_simp [hw.ne']

theorem gamma0Invariant_common_fourier_integral_eq_unit (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m : ℤ) (F : UpperHalfPlane → ℂ) (hF : Continuous F)
    (hinv : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane, F (γ.val • z) = F z)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..(N : ℝ),
      cuspFourierPhase (N : ℝ) ((gamma0CuspFrequencyStep N r : ℤ)*m) x *
        F (r⁻¹ • gamma0EisensteinHorizontalPoint y hy x)) =
      (N : ℂ)*gamma0UnitCuspFourierMean N r m F (y/(gamma0CuspTrueWidth N r : ℝ)) := by
  let w : ℝ := gamma0CuspTrueWidth N r
  let d := gamma0CuspFrequencyStep N r
  let U (x : ℝ) := cuspFourierPhase (N : ℝ) ((d : ℤ)*m) x *
    F (r⁻¹ • gamma0EisensteinHorizontalPoint y hy x)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hU : Continuous U := ((cuspFourierPhase_contDiff _ _).continuous).mul
    (hF.comp ((continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹)).comp
      (gamma0EisensteinHorizontalPoint_continuous y hy)))
  have hperiod : Function.Periodic U w := fun x => by
    dsimp only [U,d,w]
    rw [gamma0CuspCommonPhase_trueWidth_periodic N r m x]
    congr 1
    exact gamma0Invariant_rawCusp_primitive_period N r F hinv y hy x
  have hN : (d : ℝ)*w = (N : ℝ) := by
    dsimp only [d,w]
    rw [mul_comm]
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hFirst : (∫ x in (0 : ℝ)..(N : ℝ),U x) = (d : ℂ)*(∫ x in (0 : ℝ)..w,U x) := by
    simpa only [zero_add,zsmul_eq_mul,Int.cast_natCast,hN] using
      hperiod.intervalIntegral_add_zsmul_eq (d : ℤ) 0 (fun x z => hU.intervalIntegrable x z)
  have hyw : 0 < y/w := div_pos hy hw
  have hPoint (x : ℝ) : U (w*x) = cuspFourierPhase 1 m x *
      F (gamma0TrueCuspScaling N r • gamma0EisensteinHorizontalPoint (y/w) hyw x) := by
    dsimp only [U,d]
    rw [cuspFourierPhase_trueWidth,gamma0TrueCuspScaling_horizontalPoint]
    have he : w*(y/w) = y := by field_simp [hw.ne']
    congr 2
    exact UpperHalfPlane.ext (by apply Complex.ext <;> simp [gamma0EisensteinHorizontalPoint,he,w])
  have hUnit : (∫ x in (0 : ℝ)..w,U x) = (w : ℂ)*gamma0UnitCuspFourierMean N r m F (y/w) := by
    have h := intervalIntegral.smul_integral_comp_mul_left U (a := 0) (b := 1) w
    simp only [mul_zero,mul_one,Complex.real_smul] at h
    rw [← h,gamma0UnitCuspFourierMean,dite_eq_left hyw]
    simp_rw [hPoint]
  change (∫ x in (0 : ℝ)..(N : ℝ),U x) = (N : ℂ)*gamma0UnitCuspFourierMean N r m F (y/w)
  rw [hFirst,hUnit,← mul_assoc]
  congr 1
  exact_mod_cast hN

end ArtinMatthews
