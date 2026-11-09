module

public import ArtinMatthews.SpectralCuspConstantTermGlobal
public import ArtinMatthews.SpectralCuspGraphRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! The actual horizontal-average projection is the actual constant term
pulled back along cusp height. Vanishing only above a high cusp cutoff
suffices to remove its restricted tail. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem cusp_height_measurePreserving (w Y : ℝ) (hY : 0<Y) :
    MeasurePreserving UpperHalfPlane.im (volume.restrict (hyperbolicCuspStrip w Y))
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) := by
  have hs : MeasurePreserving Prod.snd (cuspStripMeasure w Y)
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) :=
    ⟨measurable_snd,Measure.map_snd_prod⟩
  exact hs.comp (cusp_coordinates_measurePreserving w Y hY)

theorem cuspHyperbolicAverageProjection_ae_constantTerm (w Y : ℝ) (hY : 0<Y)
    (U : CuspHyperbolicL2 w Y) :
    cuspHyperbolicAverageProjection w Y hY U
      =ᵐ[volume.restrict (hyperbolicCuspStrip w Y)]
        fun z => cuspHyperbolicConstantTerm w Y hY U z.im := by
  rw [cuspHyperbolicAverageProjection_factor_constantTerm]
  have hv : cuspVerticalPullback w Y (cuspHyperbolicConstantTerm w Y hY U)
      =ᵐ[cuspStripMeasure w Y] fun p => cuspHyperbolicConstantTerm w Y hY U p.2 :=
    Lp.coeFn_compMeasurePreserving _ ⟨measurable_snd,Measure.map_snd_prod⟩
  exact (cuspHyperbolicPullback_ae w Y hY _).trans
    ((cusp_coordinates_measurePreserving w Y hY).quasiMeasurePreserving.ae_eq_comp hv)

theorem gamma0CuspEnergyProjection_restricted_zero (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (u : gamma0EnergySpace N) {Y : ℝ} (hY : 1≤Y)
    (hc : gamma0CuspConstantTerm N r Y (zero_lt_one.trans_le hY) (gamma0EnergyInclusion N u)=0) :
    spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)
      (cuspHyperbolicAverageProjection (N:ℝ) 1 zero_lt_one (gamma0CuspEnergyRestriction N r u))=0 := by
  have hP := cuspHyperbolicAverageProjection_ae_constantTerm (N:ℝ) 1 zero_lt_one
    (gamma0CuspMassRestriction N r 1 zero_lt_one (gamma0EnergyInclusion N u))
  rw [gamma0CuspMassRestriction_energy,gamma0CuspHeightRestriction_one] at hP
  have hP' := (Measure.absolutelyContinuous_of_le (spectralCuspHyperbolicMeasure_mono hY)).ae_eq hP
  have hC := gamma0CuspConstantTerm_height_ae N r 1 Y zero_lt_one (zero_lt_one.trans_le hY) hY
    (gamma0EnergyInclusion N u)
  rw [hc] at hC
  have hzero := hC.trans (Lp.coeFn_zero ℂ 2 ((cuspHorizontalMeasure (N:ℝ) univ) • cuspVerticalMeasure Y))
  have hz := (cusp_height_measurePreserving (N:ℝ) Y (zero_lt_one.trans_le hY)).quasiMeasurePreserving.ae_eq_comp hzero
  apply Lp.ext
  filter_upwards [spectralLpMeasureRestriction_ae (spectralCuspHyperbolicMeasure_mono hY)
    (cuspHyperbolicAverageProjection (N:ℝ) 1 zero_lt_one (gamma0CuspEnergyRestriction N r u)),
    hP',hz,Lp.coeFn_zero ℂ 2 (volume.restrict (hyperbolicCuspStrip (N:ℝ) Y))]
    with z hr hp hc hz0
  rw [hr,hp]
  have he : cuspHyperbolicConstantTerm (N:ℝ) 1 zero_lt_one
      (gamma0CuspEnergyRestriction N r u) z.im=
      gamma0CuspConstantTerm N r 1 zero_lt_one (gamma0EnergyInclusion N u) z.im := by
    change _=cuspHyperbolicConstantTerm (N:ℝ) 1 zero_lt_one
      (gamma0CuspMassRestriction N r 1 zero_lt_one (gamma0EnergyInclusion N u)) z.im
    rw [gamma0CuspMassRestriction_energy,gamma0CuspHeightRestriction_one]
  rw [he]
  exact hc.trans hz0.symm

end ArtinMatthews
