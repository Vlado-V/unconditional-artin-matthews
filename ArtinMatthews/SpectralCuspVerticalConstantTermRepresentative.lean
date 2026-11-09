module

public import ArtinMatthews.SpectralCuspConstantTermRepresentative
public import ArtinMatthews.SpectralHorizontalPeriodMeasurableFibers


set_option backward.privateInPublic true
@[expose] public section

/-! The actual vertical constant-term derivative.  It is the normalized mean
of the physical vertical derivative, obtained by dividing the proved
height-scaled derivative by positive height. -/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

def gamma0CuspSeedVerticalPlaneExtension (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (p : ℝ × ℝ) : ℂ :=
  p.2 • fderiv ℝ (gamma0CuspSeedPlaneExtension N ψ r Y) p (0, 1)

theorem gamma0CuspSeedVerticalPlaneExtension_continuous (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    Continuous (gamma0CuspSeedVerticalPlaneExtension N ψ r Y) := by
  have hs := spectralSectionSmoothExtension_contDiff hY _ (gamma0CuspSection_smooth N ψ r)
  exact continuous_snd.smul ((hs.continuous_fderiv (by simp)).clm_apply continuous_const)

theorem gamma0CuspSeedVerticalPlaneExtension_at_upper (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (z : UpperHalfPlane) (hz : Y < z.im) :
    gamma0CuspSeedVerticalPlaneExtension N ψ r Y (z.re, z.im) = gamma0CuspVerticalField N ψ r z := by
  let F := gamma0CuspSection N ψ r
  have he : gamma0CuspSeedPlaneExtension N ψ r Y =ᶠ[𝓝 (z.re, z.im)] spectralSectionPlane F := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hz] with p hp
    exact spectralSectionSmoothExtension_eq hY F hp.le
  have hd := he.fderiv_eq (𝕜 := ℝ)
  change z.im • fderiv ℝ (gamma0CuspSeedPlaneExtension N ψ r Y) (z.re, z.im) (0, 1) = _
  rw [hd]
  have hdiff := (spectralSectionPlane_contDiffAt F (gamma0CuspSection_smooth N ψ r)
    (p := (z.re, z.im)) z.im_pos).differentiableAt
    (by simp)
  rw [← spectralPlanePartialY_eq_fderiv hdiff]
  rw [(spectralSectionPlane_coordinate_derivatives F (gamma0CuspSection_smooth N ψ r)
    (p := (z.re, z.im)) z.im_pos).2]
  have hcoords : Complex.equivRealProdCLM.symm (z.re, z.im) = (z : ℂ) :=
    Complex.equivRealProdCLM.symm_apply_apply (z : ℂ)
  rw [hcoords]
  exact (gamma0CuspVerticalField_apply N ψ r z).symm

theorem gamma0CuspVerticalConstantTerm_seed_ae (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    gamma0CuspVerticalConstantTerm N r Y hY (gamma0EnergyTest N ψ)
      =ᵐ[cuspVerticalMeasure Y]
        cuspHorizontalMean (N : ℝ) (gamma0CuspSeedVerticalPlaneExtension N ψ r Y) := by
  let K := gamma0CuspSeedVerticalPlaneExtension N ψ r Y
  have hS : MeasurableSet (hyperbolicCuspStrip (N : ℝ) Y) :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have hae : gamma0CuspVerticalField N ψ r
      =ᵐ[volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)]
        (fun z : UpperHalfPlane => K (z.re, z.im)) := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact (gamma0CuspSeedVerticalPlaneExtension_at_upper N ψ r Y hY z hz.2).symm
  have hm := (memLp_congr_ae hae).mp (gamma0CuspVerticalField_memLp N ψ r Y hY)
  have he : hm.toLp (fun z : UpperHalfPlane => K (z.re, z.im)) =
      gamma0CuspVerticalSeedLp N ψ r Y hY := by
    apply Lp.ext
    exact hm.coeFn_toLp.trans (hae.symm.trans (gamma0CuspVerticalSeedLp_ae N ψ r Y hY).symm)
  change cuspHyperbolicConstantTerm (N : ℝ) Y hY
    (gamma0CuspVerticalRestriction N r Y hY (gamma0EnergyTest N ψ)) =ᵐ[_] _
  rw [gamma0CuspVerticalRestriction_apply, ← he]
  exact cuspHyperbolicConstantTerm_ae_representative (N : ℝ) Y
    (Nat.cast_pos.mpr (NeZero.pos N)) hY K
      (gamma0CuspSeedVerticalPlaneExtension_continuous N ψ r Y hY) hm

def gamma0CuspConstantTermDerivative (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (u : gamma0EnergySpace N) (y : ℝ) : ℂ :=
  y⁻¹ • gamma0CuspVerticalConstantTerm N r Y hY u y

theorem gamma0CuspConstantTermDerivative_seed_ae (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    gamma0CuspConstantTermDerivative N r Y hY (gamma0EnergyTest N ψ)
      =ᵐ[cuspVerticalMeasure Y] cuspHorizontalMean (N : ℝ)
        (fun p => fderiv ℝ (gamma0CuspSeedPlaneExtension N ψ r Y) p (0, 1)) := by
  have hy : ∀ᵐ y ∂cuspVerticalMeasure Y, Y < y :=
    (spectralHorizontal_cuspVertical_ae_iff hY).mpr (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [gamma0CuspVerticalConstantTerm_seed_ae N ψ r Y hY, hy] with y he hy
  change y⁻¹ • gamma0CuspVerticalConstantTerm N r Y hY (gamma0EnergyTest N ψ) y = _
  rw [he]
  have hm : cuspHorizontalMean (N : ℝ) (gamma0CuspSeedVerticalPlaneExtension N ψ r Y) y =
      y • cuspHorizontalMean (N : ℝ)
        (fun p => fderiv ℝ (gamma0CuspSeedPlaneExtension N ψ r Y) p (0, 1)) y := by
    unfold cuspHorizontalMean
    simp only [gamma0CuspSeedVerticalPlaneExtension, Complex.real_smul]
    rw [integral_const_mul]
    ring
  rw [hm, smul_smul, inv_mul_cancel₀ (hY.trans hy).ne', one_smul]

theorem gamma0CuspConstantTermDerivative_memLp (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (u : gamma0EnergySpace N) :
    MemLp (gamma0CuspConstantTermDerivative N r Y hY u) 2
      ((cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure Y) := by
  have hb := Lp.memLp (gamma0CuspVerticalConstantTerm N r Y hY u)
  apply hb.of_le_mul
    (measurable_inv.aestronglyMeasurable.smul hb.aestronglyMeasurable)
  have hy : ∀ᵐ y ∂cuspVerticalMeasure Y, Y < y :=
    (spectralHorizontal_cuspVertical_ae_iff hY).mpr (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [Measure.ae_smul_measure hy (cuspHorizontalMeasure (N : ℝ) univ)] with y hy
  change ‖y⁻¹ • gamma0CuspVerticalConstantTerm N r Y hY u y‖ ≤
    Y⁻¹ * ‖gamma0CuspVerticalConstantTerm N r Y hY u y‖
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hY.trans hy).le)]
  have hi : y⁻¹ ≤ Y⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hY hy.le
  exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)

end ArtinMatthews
