module

public import ArtinMatthews.SpectralCuspTwoCellRepresentative
public import ArtinMatthews.SpectralCuspConstantTermRepresentative
public import ArtinMatthews.SpectralHorizontalPeriodMeasurableFibers


set_option backward.privateInPublic true
@[expose] public section

/-! Actual two-cell hyperbolic representatives of the completed full mass space. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ENNReal MatrixGroups
noncomputable section

theorem cuspStripMeasure_height_mem {Y : ℝ} (hY : 0 < Y) (w : ℝ) :
    ∀ᵐ p ∂cuspStripMeasure w Y, Y < p.2 := by
  have hy : ∀ᵐ y ∂cuspVerticalMeasure Y, Y < y :=
    (spectralHorizontal_cuspVertical_ae_iff hY).mpr (ae_restrict_mem measurableSet_Ioi)
  exact (Measure.quasiMeasurePreserving_snd (μ := cuspHorizontalMeasure w)
    (ν := cuspVerticalMeasure Y)).ae hy

theorem cuspTwoCellExtension_ae_periodic {w Y : ℝ} (hw : 0 ≤ w) (hY : 0 < Y)
    (F : ℝ × ℝ → ℂ) (hF : MemLp F 2 (cuspStripMeasure w Y))
    (hperiod : ∀ p : ℝ × ℝ, Y < p.2 → F (p.1 + w, p.2) = F p) :
    cuspTwoCellExtension hw Y (hF.toLp F) =ᵐ[cuspStripMeasure (2 * w) Y] F := by
  have hf : hF.toLp F =ᵐ[(2 : ℝ≥0∞) • cuspStripMeasure w Y] F :=
    Measure.ae_smul_measure hF.coeFn_toLp 2
  have hp := (spectralTwoCellCoordinateFold_preserving hw Y).quasiMeasurePreserving.ae_eq_comp hf
  refine (cuspTwoCellExtension_ae hw Y _).trans (hp.trans ?_)
  filter_upwards [cuspStripMeasure_height_mem hY (2 * w)] with p hpy
  change F (spectralTwoCellFold w p.1, p.2) = F p
  by_cases hx : p.1 ≤ w
  · simp [spectralTwoCellFold_first hx]
  · rw [spectralTwoCellFold_second (lt_of_not_ge hx)]
    have h := hperiod (p.1 - w, p.2) hpy
    simpa only [sub_add_cancel, Prod.eta] using h.symm

theorem gamma0CuspSeedPlaneExtension_periodic (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) {Y : ℝ} (hY : 0 < Y)
    (p : ℝ × ℝ) (hp : Y < p.2) :
    gamma0CuspSeedPlaneExtension N ψ r Y (p.1 + N, p.2) =
      gamma0CuspSeedPlaneExtension N ψ r Y p := by
  unfold gamma0CuspSeedPlaneExtension
  rw [spectralSectionSmoothExtension_eq hY _ (p := (p.1 + N, p.2)) hp.le,
    spectralSectionSmoothExtension_eq hY _ (p := p) hp.le]
  simpa only [spectralSectionPlane, gamma0CuspSection, Complex.equivRealProdCLM_symm_apply]
    using gamma0PoincareSeed_cusp_periodic N ψ.val r (hY.trans hp) p.1

def gamma0CuspTwoCellCoordinateRestriction (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    Gamma0RegionL2 N →L[ℝ] CuspStripL2 (2 * (N : ℝ)) Y :=
  (cuspTwoCellExtension (Nat.cast_nonneg N) Y).comp
    (((cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint.restrictScalars ℝ).comp
      ((gamma0CuspMassRestriction N r Y hY).restrictScalars ℝ))

def gamma0CuspTwoCellMassRestriction (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    Gamma0RegionL2 N →L[ℝ] CuspHyperbolicL2 (2 * (N : ℝ)) Y :=
  ((cuspHyperbolicPullback (2 * (N : ℝ)) Y hY).toContinuousLinearMap.restrictScalars ℝ).comp
    (gamma0CuspTwoCellCoordinateRestriction N r Y hY)

theorem gamma0CuspCoordinateRestriction_seed (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds) :
    ∃ hF : MemLp (gamma0CuspSeedPlaneExtension N ψ r Y) 2 (cuspStripMeasure (N : ℝ) Y),
      (cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint
        (gamma0CuspMassRestriction N r Y hY (gamma0SmoothSeedMass N ψ)) =
          hF.toLp (gamma0CuspSeedPlaneExtension N ψ r Y) := by
  let F := gamma0CuspSeedPlaneExtension N ψ r Y
  have hc : Continuous F :=
    (spectralSectionSmoothExtension_contDiff hY _ (gamma0CuspSection_smooth N ψ r)).continuous
  have hh := gamma0CuspSeedPlaneExtension_memLp N ψ r Y hY
  have hp := (cuspHyperbolic_memLp_iff (N : ℝ) Y hY F hc).mpr hh
  refine ⟨hp, ?_⟩
  have he : gamma0CuspMassRestriction N r Y hY (gamma0SmoothSeedMass N ψ) =
      hh.toLp (fun z : UpperHalfPlane => F (z.re, z.im)) := by
    apply Lp.ext
    filter_upwards [gamma0CuspMassRestriction_seed_ae N r Y hY ψ, hh.coeFn_toLp,
      ae_restrict_mem ((measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
        (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable))] with z hz hf hmem
    rw [hz, hf]
    exact (spectralSectionSmoothExtension_at_upper hY _ z hmem.2.le).symm
  rw [he, ← cuspHyperbolicPullback_toLp (N : ℝ) Y hY F hp hh,
    cuspHyperbolicPullback_adjoint_self]

theorem gamma0CuspTwoCellCoordinateRestriction_seed_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds) :
    gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0SmoothSeedMass N ψ)
      =ᵐ[cuspStripMeasure (2 * (N : ℝ)) Y] gamma0CuspSeedPlaneExtension N ψ r Y := by
  obtain ⟨hp, he⟩ := gamma0CuspCoordinateRestriction_seed N r Y hY ψ
  change cuspTwoCellExtension (Nat.cast_nonneg N) Y
    ((cuspHyperbolicPullback (N : ℝ) Y hY).toContinuousLinearMap.adjoint
      (gamma0CuspMassRestriction N r Y hY (gamma0SmoothSeedMass N ψ))) =ᵐ[_] _
  rw [he]
  exact cuspTwoCellExtension_ae_periodic (Nat.cast_nonneg N) hY _ hp
    (gamma0CuspSeedPlaneExtension_periodic N ψ r hY)

theorem gamma0CuspTwoCellMassRestriction_seed_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds) :
    gamma0CuspTwoCellMassRestriction N r Y hY (gamma0SmoothSeedMass N ψ)
      =ᵐ[volume.restrict (hyperbolicCuspStrip (2 * (N : ℝ)) Y)] gamma0CuspSection N ψ r := by
  have ha := (cusp_coordinates_measurePreserving (2 * (N : ℝ)) Y hY).quasiMeasurePreserving.ae_eq_comp
    (gamma0CuspTwoCellCoordinateRestriction_seed_ae N r Y hY ψ)
  change cuspHyperbolicPullback (2 * (N : ℝ)) Y hY
    (gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0SmoothSeedMass N ψ)) =ᵐ[_] _
  refine (cuspHyperbolicPullback_ae _ _ _ _).trans (ha.trans ?_)
  filter_upwards [ae_restrict_mem ((measurableSet_Ioc.preimage UpperHalfPlane.continuous_re.measurable).inter
    (measurableSet_Ioi.preimage UpperHalfPlane.continuous_im.measurable))] with z hz
  exact spectralSectionSmoothExtension_at_upper hY _ z hz.2.le

end
end ArtinMatthews
