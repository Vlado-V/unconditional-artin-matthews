module

public import ArtinMatthews.SpectralCuspInteriorParseval
public import ArtinMatthews.SpectralCuspSeparableCoordinates
public import ArtinMatthews.SpectralGamma0FourierEnergy
public import ArtinMatthews.SpectralCuspConstantTermOperator


set_option backward.privateInPublic true
@[expose] public section

/-! The actual full Fourier projections detect completed cusp-strip mass,
by slice Parseval and the genuine hyperbolic coordinate pullback. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ENNReal

namespace ArtinMatthews

theorem cuspFourierProjection_all_eq_zero (w Y : ℝ) (hw : 0 < w)
    (F : CuspStripL2 w Y) (h : ∀ n : ℤ, cuspFourierProjection w Y w n F = 0) : F = 0 := by
  have hFn := Lp.aestronglyMeasurable F
  have hI := (memLp_two_iff_integrable_sq_norm hFn).mp (Lp.memLp F)
  have hslice : ∀ᵐ y ∂cuspVerticalMeasure Y,
      MemLp (fun x : ℝ => F (x,y)) 2 (cuspHorizontalMeasure w) := by
    filter_upwards [hFn.prodMk_right, hI.prod_left_ae] with y hy hiy
    exact (memLp_two_iff_integrable_sq_norm hy).mpr hiy
  have hzero (n : ℤ) : ∀ᵐ y ∂cuspVerticalMeasure Y,
      cuspHorizontalWeightedMean w (cuspFourierPhase w n) F y = 0 := by
    have hz : (cuspFourierProjection w Y w n F : ℝ → ℂ) =ᵐ[cuspVerticalMeasure Y] 0 := by
      rw [h n]
      apply (Measure.ae_ennreal_smul_measure_iff (μ := cuspVerticalMeasure Y)
        (show cuspHorizontalMeasure w univ ≠ 0 by
          rw [cuspHorizontalMeasure_univ]
          exact (ENNReal.ofReal_pos.mpr hw).ne')).mp
      exact Lp.coeFn_zero ℂ 2 _
    exact (cuspFourierProjection_ae w Y w hw n F).symm.trans hz
  have hz : ∀ᵐ y ∂cuspVerticalMeasure Y, ∫ x, ‖F (x,y)‖^2 ∂cuspHorizontalMeasure w = 0 := by
    filter_upwards [hslice, ae_all_iff.mpr hzero] with y hy hz
    have hCoeff (n : ℤ) : fourierCoeffOn hw (fun x => F (x,y)) n = 0 := by
      have he := hz n
      unfold cuspHorizontalWeightedMean cuspHorizontalMean at he
      rw [fourierCoeffOn_eq_integral]
      simp_rw [← cuspFourierPhase_eq_addCircle_fourier (w - 0) (by simpa using hw) n]
      simpa only [sub_zero, intervalIntegral.integral_of_le hw.le, Complex.real_smul,
        one_div, smul_eq_mul, Complex.ofReal_inv] using he
    have hp := hasSum_sq_fourierCoeffOn hw hy
    simp only [hCoeff, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      sub_zero, smul_eq_mul] at hp
    have hp₀ := hp.unique (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℝ)) 0)
    rw [intervalIntegral.integral_of_le hw.le] at hp₀
    exact (mul_eq_zero.mp hp₀).resolve_left (inv_ne_zero hw.ne')
  have hzI : ∫ p, ‖F p‖^2 ∂cuspStripMeasure w Y = 0 := by
    change ∫ p, ‖F p‖^2 ∂(cuspHorizontalMeasure w).prod (cuspVerticalMeasure Y) = 0
    rw [integral_prod_symm _ hI]
    exact integral_eq_zero_of_ae hz
  have hzF := (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg ‖F p‖) hI).mp hzI
  apply Lp.ext
  filter_upwards [hzF, Lp.coeFn_zero ℂ 2 (cuspStripMeasure w Y)] with p hp hzLp
  exact (norm_eq_zero.mp ((sq_eq_zero_iff).mp hp)).trans hzLp.symm

theorem cuspHyperbolicPullback_surjective (w Y : ℝ) (hY : 0 < Y) :
    Function.Surjective (cuspHyperbolicPullback w Y hY) := by
  intro f
  let F (p : ℝ × ℝ) := f (UpperHalfPlane.ofComplex ((p.1 : ℂ) + p.2 * Complex.I))
  let coord (z : UpperHalfPlane) := (z.re,z.im)
  have hp := cusp_coordinates_measurePreserving w Y hY
  have hFz (z : UpperHalfPlane) : F (coord z) = f z := by
    have he : (z.re : ℂ) + z.im * Complex.I = (z : ℂ) := Complex.re_add_im _
    simp only [F, coord, he, UpperHalfPlane.ofComplex_apply]
  have hF : MemLp F 2 (cuspStripMeasure w Y) := by
    rw [← hp.map_eq]
    apply cusp_coordinates_measurableEmbedding.memLp_map_measure_iff.mpr
    have he : F ∘ (fun z : UpperHalfPlane => (z.re,z.im)) = f := funext hFz
    rw [he]
    exact Lp.memLp f
  refine ⟨hF.toLp F, ?_⟩
  apply Lp.ext
  have h₁ := cuspHyperbolicPullback_ae w Y hY (hF.toLp F)
  have h₂ := hp.quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp
  filter_upwards [h₁, h₂] with z hz hz'
  exact hz.trans (hz'.trans (hFz z))

theorem gamma0CuspMassRestriction_eq_zero_of_fourier_eq_zero (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (f : Gamma0RegionL2 N)
    (h : ∀ n : ℤ, gamma0CuspFourierCoefficient N r Y hY n f = 0) :
    gamma0CuspMassRestriction N r Y hY f = 0 := by
  obtain ⟨F, hF⟩ := cuspHyperbolicPullback_surjective (N : ℝ) Y hY
    (gamma0CuspMassRestriction N r Y hY f)
  have hz : F = 0 := by
    apply cuspFourierProjection_all_eq_zero _ _ (Nat.cast_pos.mpr (NeZero.pos N))
    intro n
    have hn := h n
    unfold gamma0CuspFourierCoefficient at hn
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ← hF,
      cuspHyperbolicPullback_adjoint_self] at hn
    exact hn
  rw [← hF, hz, map_zero]

theorem gamma0CuspFourierCoefficient_zero_eq_constantTerm (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (f : Gamma0RegionL2 N) :
    gamma0CuspFourierCoefficient N r Y hY 0 f = gamma0CuspConstantTerm N r Y hY f := by
  have hm (u : CuspStripL2 (N : ℝ) Y) : cuspFourierMultiplier (N : ℝ) Y (N : ℝ) 0 u = u := by
    apply Lp.ext
    filter_upwards [cuspFourierMultiplyLp_ae (N : ℝ) Y (N : ℝ) 0 u] with p hp
    change cuspFourierMultiplyLp (N : ℝ) Y (N : ℝ) 0 u p = u p
    simpa only [cuspFourierPhase, cuspFourierFrequency, Int.cast_zero, mul_zero, zero_div,
      Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] using hp
  simp only [gamma0CuspFourierCoefficient, gamma0CuspConstantTerm, cuspHyperbolicConstantTerm,
    cuspFourierProjection, ContinuousLinearMap.coe_comp', Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, hm]

end ArtinMatthews
