module

public import ArtinMatthews.SpectralCuspFourierProjection
public import ArtinMatthews.SpectralCuspTwoCellHyperbolic
public import ArtinMatthews.SpectralCuspVerticalConstantTermRepresentative


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Fourier projection of the completed cusp mass and vertical
energy restrictions.  The phase period is N; no point values are chosen
for completed L² classes. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal MatrixGroups ContDiff

namespace ArtinMatthews

def gamma0CuspFourierCoefficient (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) :
    Gamma0RegionL2 N →L[ℂ] CuspVerticalL2 (N : ℝ) Y :=
  (cuspFourierProjection (N : ℝ) Y (N : ℝ) n).comp
    ((cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint.comp
      (gamma0CuspMassRestriction N r Y hY))

def gamma0CuspFourierScaledDerivative (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) :
    gamma0EnergySpace N →L[ℂ] CuspVerticalL2 (N : ℝ) Y :=
  (cuspFourierProjection (N : ℝ) Y (N : ℝ) n).comp
    ((cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint.comp
      (gamma0CuspVerticalRestriction N r Y hY))

def gamma0CuspFourierDerivative (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ)
    (u : gamma0EnergySpace N) (y : ℝ) : ℂ :=
  y⁻¹ • gamma0CuspFourierScaledDerivative N r Y hY n u y

theorem gamma0CuspFourierCoefficient_integrable_mass (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (f : Gamma0RegionL2 N) :
    IntegrableOn (fun y : ℝ => ‖gamma0CuspFourierCoefficient N r Y hY n f y‖ ^ 2 / y ^ 2)
      (Ioi Y) :=
  cuspVerticalL2_integrable_energy (Nat.cast_pos.mpr (NeZero.pos N)) hY _

theorem gamma0CuspFourierDerivative_integrable_energy (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (u : gamma0EnergySpace N) :
    IntegrableOn (fun y : ℝ => ‖gamma0CuspFourierDerivative N r Y hY n u y‖ ^ 2)
      (Ioi Y) := by
  have hi := cuspVerticalL2_integrable_energy (Nat.cast_pos.mpr (NeZero.pos N)) hY
    (gamma0CuspFourierScaledDerivative N r Y hY n u)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 < y := hY.trans hy
  rw [gamma0CuspFourierDerivative, norm_smul, Real.norm_of_nonneg (by positivity)]
  simp only [mul_pow, inv_pow, div_eq_mul_inv]
  ring

theorem gamma0CuspFourierCoefficient_seed_ae (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) :
    gamma0CuspFourierCoefficient N r Y hY n (gamma0SmoothSeedMass N ψ)
      =ᵐ[cuspVerticalMeasure Y] cuspHorizontalWeightedMean (N : ℝ)
        (cuspFourierPhase (N : ℝ) n) (gamma0CuspSeedPlaneExtension N ψ r Y) := by
  obtain ⟨hp, he⟩ := gamma0CuspCoordinateRestriction_seed N r Y hY ψ
  change cuspFourierProjection (N : ℝ) Y (N : ℝ) n
    ((cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint
      (gamma0CuspMassRestriction N r Y hY (gamma0SmoothSeedMass N ψ))) =ᵐ[_] _
  rw [he]
  refine (cuspFourierProjection_ae (N : ℝ) Y (N : ℝ)
    (Nat.cast_pos.mpr (NeZero.pos N)) n _).trans ?_
  apply cuspHorizontalMean_congr_ae
  filter_upwards [hp.coeFn_toLp] with p hp
  exact congrArg (fun z => cuspFourierPhase (N : ℝ) n p.1 * z) hp

theorem gamma0CuspCoordinateVerticalRestriction_seed (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ hp : MemLp (gamma0CuspSeedVerticalPlaneExtension N ψ r Y) 2
        (cuspStripMeasure (N : ℝ) Y),
      (cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint
        (gamma0CuspVerticalRestriction N r Y hY (gamma0EnergyTest N ψ)) =
          hp.toLp (gamma0CuspSeedVerticalPlaneExtension N ψ r Y) := by
  let K := gamma0CuspSeedVerticalPlaneExtension N ψ r Y
  have hc : Continuous K := gamma0CuspSeedVerticalPlaneExtension_continuous N ψ r Y hY
  have hae : gamma0CuspVerticalField N ψ r
      =ᵐ[volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)]
        fun z : UpperHalfPlane => K (z.re, z.im) := by
    filter_upwards [ae_restrict_mem
      ((measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
        (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable))] with z hz
    exact (gamma0CuspSeedVerticalPlaneExtension_at_upper N ψ r Y hY z hz.2).symm
  have hh := (memLp_congr_ae hae).mp (gamma0CuspVerticalField_memLp N ψ r Y hY)
  have hp := (cuspHyperbolic_memLp_iff (N : ℝ) Y hY K hc).mpr hh
  refine ⟨hp, ?_⟩
  have he : gamma0CuspVerticalSeedLp N ψ r Y hY =
      hh.toLp (fun z : UpperHalfPlane => K (z.re, z.im)) := by
    apply Lp.ext
    exact (gamma0CuspVerticalSeedLp_ae N ψ r Y hY).trans (hae.trans hh.coeFn_toLp.symm)
  rw [gamma0CuspVerticalRestriction_apply, he,
    ← cuspHyperbolicPullback_toLp (N : ℝ) Y hY K hp hh,
    cuspHyperbolicPullback_adjoint_self]

theorem gamma0CuspFourierScaledDerivative_seed_ae (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) :
    gamma0CuspFourierScaledDerivative N r Y hY n (gamma0EnergyTest N ψ)
      =ᵐ[cuspVerticalMeasure Y] cuspHorizontalWeightedMean (N : ℝ)
        (cuspFourierPhase (N : ℝ) n) (gamma0CuspSeedVerticalPlaneExtension N ψ r Y) := by
  obtain ⟨hp, he⟩ := gamma0CuspCoordinateVerticalRestriction_seed N ψ r Y hY
  change cuspFourierProjection (N : ℝ) Y (N : ℝ) n
    ((cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint
      (gamma0CuspVerticalRestriction N r Y hY (gamma0EnergyTest N ψ))) =ᵐ[_] _
  rw [he]
  refine (cuspFourierProjection_ae (N : ℝ) Y (N : ℝ)
    (Nat.cast_pos.mpr (NeZero.pos N)) n _).trans ?_
  apply cuspHorizontalMean_congr_ae
  filter_upwards [hp.coeFn_toLp] with p hp
  exact congrArg (fun z => cuspFourierPhase (N : ℝ) n p.1 * z) hp

theorem gamma0CuspFourierDerivative_seed_ae (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) :
    gamma0CuspFourierDerivative N r Y hY n (gamma0EnergyTest N ψ)
      =ᵐ[cuspVerticalMeasure Y] cuspHorizontalWeightedMean (N : ℝ)
        (cuspFourierPhase (N : ℝ) n)
        (fun p => fderiv ℝ (gamma0CuspSeedPlaneExtension N ψ r Y) p (0, 1)) := by
  have hy : ∀ᵐ y ∂cuspVerticalMeasure Y, Y < y :=
    (spectralHorizontal_cuspVertical_ae_iff hY).mpr (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [gamma0CuspFourierScaledDerivative_seed_ae N ψ r Y hY n, hy] with y he hy
  change y⁻¹ • gamma0CuspFourierScaledDerivative N r Y hY n (gamma0EnergyTest N ψ) y = _
  rw [he]
  have hm : cuspHorizontalWeightedMean (N : ℝ) (cuspFourierPhase (N : ℝ) n)
      (gamma0CuspSeedVerticalPlaneExtension N ψ r Y) y =
      y • cuspHorizontalWeightedMean (N : ℝ) (cuspFourierPhase (N : ℝ) n)
        (fun p => fderiv ℝ (gamma0CuspSeedPlaneExtension N ψ r Y) p (0, 1)) y := by
    unfold cuspHorizontalWeightedMean cuspHorizontalMean
    simp only [gamma0CuspSeedVerticalPlaneExtension, Complex.real_smul]
    calc
      _ = ((N : ℝ) : ℂ)⁻¹ * ((y : ℂ) *
          ∫ x in Ioc (0 : ℝ) (N : ℝ), cuspFourierPhase (N : ℝ) n x *
            fderiv ℝ (gamma0CuspSeedPlaneExtension N ψ r Y) (x, y) (0, 1)) := by
        congr 1
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x _
        ring
      _ = _ := by ring
  rw [hm, smul_smul, inv_mul_cancel₀ (hY.trans hy).ne', one_smul]

end ArtinMatthews
