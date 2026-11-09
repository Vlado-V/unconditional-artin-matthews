module

public import ArtinMatthews.SpectralCuspConstantTermOperator
public import ArtinMatthews.SpectralSectionPlaneSmoothExtension


set_option backward.privateInPublic true
@[expose] public section

/-! The actual constant-term Hilbert operator equals the literal normalized
horizontal integral, with no choice of point values of an L² class. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem cuspHyperbolicConstantTerm_ae_representative (w Y : ℝ)
    (hw : 0 < w) (hY : 0 < Y) (F : ℝ × ℝ → ℂ) (hF : Continuous F)
    (hh : MemLp (fun z : UpperHalfPlane => F (z.re, z.im)) 2
      (volume.restrict (hyperbolicCuspStrip w Y))) :
    cuspHyperbolicConstantTerm w Y hY (hh.toLp (fun z : UpperHalfPlane => F (z.re, z.im)))
      =ᵐ[cuspVerticalMeasure Y] cuspHorizontalMean w F := by
  have hp := (cuspHyperbolic_memLp_iff w Y hY F hF).mpr hh
  have hU : (cuspHyperbolicPullback w Y hY).toContinuousLinearMap.adjoint
      (hh.toLp (fun z : UpperHalfPlane => F (z.re, z.im))) = hp.toLp F := by
    rw [← cuspHyperbolicPullback_toLp w Y hY F hp hh]
    exact cuspHyperbolicPullback_adjoint_self w Y hY _
  change ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint
    ((cuspHyperbolicPullback w Y hY).toContinuousLinearMap.adjoint
      (hh.toLp (fun z : UpperHalfPlane => F (z.re, z.im)))) : ℝ → ℂ) =ᵐ[_] _
  rw [hU]
  exact (cuspVerticalAdjoint_ae_horizontalMean w Y hw (hp.toLp F)).trans
    (cuspHorizontalMean_congr_ae w Y hp.coeFn_toLp)

def gamma0CuspSeedPlaneExtension (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (Y : ℝ) : ℝ × ℝ → ℂ :=
  spectralSectionSmoothExtension Y (gamma0CuspSection N ψ r)

theorem gamma0CuspSeedPlaneExtension_memLp (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    MemLp (fun z : UpperHalfPlane => gamma0CuspSeedPlaneExtension N ψ r Y (z.re, z.im)) 2
      (volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)) := by
  have hS : MeasurableSet (hyperbolicCuspStrip (N : ℝ) Y) :=
    (measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
      (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable)
  have he : gamma0CuspSection N ψ r =ᵐ[volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)]
      (fun z : UpperHalfPlane => gamma0CuspSeedPlaneExtension N ψ r Y (z.re, z.im)) := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact (spectralSectionSmoothExtension_at_upper hY (gamma0CuspSection N ψ r) z hz.2.le).symm
  exact (memLp_congr_ae he).mp (gamma0CuspSection_memLp_positive_height N ψ r Y hY)

theorem gamma0CuspConstantTerm_seed_ae (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    gamma0CuspConstantTerm N r Y hY (gamma0SmoothSeedMass N ψ)
      =ᵐ[cuspVerticalMeasure Y]
        cuspHorizontalMean (N : ℝ) (gamma0CuspSeedPlaneExtension N ψ r Y) := by
  let F := gamma0CuspSeedPlaneExtension N ψ r Y
  have hc : Continuous F :=
    (spectralSectionSmoothExtension_contDiff hY _ (gamma0CuspSection_smooth N ψ r)).continuous
  have hm := gamma0CuspSeedPlaneExtension_memLp N ψ r Y hY
  have he : hm.toLp (fun z : UpperHalfPlane => F (z.re, z.im)) =
      gamma0CuspHeightSeedLp N r Y hY ψ := by
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp, gamma0CuspHeightSeedLp_ae N r Y hY ψ,
      ae_restrict_mem ((measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
        (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable))] with z hF hψ hz
    rw [hF, hψ]
    exact spectralSectionSmoothExtension_at_upper hY _ z hz.2.le
  change cuspHyperbolicConstantTerm (N : ℝ) Y hY
    (gamma0CuspMassRestriction N r Y hY (gamma0SmoothSeedMass N ψ)) =ᵐ[_] _
  rw [gamma0CuspMassRestriction_apply, ← he]
  exact cuspHyperbolicConstantTerm_ae_representative (N : ℝ) Y
    (Nat.cast_pos.mpr (NeZero.pos N)) hY F hc hm

end ArtinMatthews
