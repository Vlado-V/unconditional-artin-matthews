module

public import ArtinMatthews.SpectralGamma0EllipticBand
public import ArtinMatthews.CuspAverageHyperbolicTransport
public import ArtinMatthews.SpectralCuspTwoCellHyperbolic
public import Mathlib.MeasureTheory.Measure.OpenPos


set_option backward.privateInPublic true
@[expose] public section

/-! Exact almost-everywhere period transport and pointwise periodicity of
continuous representatives, using both actual adjacent cusp cells. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

theorem cuspStrip_volume_absolutelyContinuous (w : ℝ) {Y : ℝ} (hY : 0 < Y) :
    volume.restrict (Ioc 0 w ×ˢ Ioi Y) ≪ cuspStripMeasure w Y := by
  rw [cuspStripMeasure_eq_density]
  apply withDensity_absolutelyContinuous' (by fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with p hp
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (zpow_pos (hY.trans hp.2) _))

theorem gamma0CuspTwoCellCoordinateRestriction_shift_ae
    (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (f : Gamma0RegionL2 N) :
    (fun p : ℝ × ℝ => gamma0CuspTwoCellCoordinateRestriction N r Y hY f (p.1+N,p.2))
      =ᵐ[cuspStripMeasure (N:ℝ) Y] gamma0CuspTwoCellCoordinateRestriction N r Y hY f := by
  exact cuspTwoCellExtension_shift_ae (Nat.cast_nonneg N) Y _

theorem gamma0CuspTwoCellCoordinateRestriction_shift_volume_ae
    (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (f : Gamma0RegionL2 N) :
    (fun p : ℝ × ℝ => gamma0CuspTwoCellCoordinateRestriction N r Y hY f (p.1+N,p.2))
      =ᵐ[volume.restrict (Ioc 0 (N:ℝ) ×ˢ Ioi Y)]
      gamma0CuspTwoCellCoordinateRestriction N r Y hY f :=
  (cuspStrip_volume_absolutelyContinuous (N:ℝ) hY).ae_eq
    (gamma0CuspTwoCellCoordinateRestriction_shift_ae N r Y hY f)

theorem gamma0CuspTwoCell_real_representative_periodic
    (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (f : Gamma0RegionL2 N)
    (L : ℂ →L[ℝ] ℝ) (g : (Fin 2 → ℝ) → ℝ)
    (hg : ContinuousOn g {x | 0 < x 0 ∧ x 0 < 2*(N:ℝ) ∧ Y < x 1})
    (hgf : ∀ᵐ x ∂volume, (0 < x 0 ∧ x 0 < 2*(N:ℝ) ∧ Y < x 1) →
      g x = L (gamma0CuspTwoCellCoordinateRestriction N r Y hY f (spectralEllipticCoordinates x))) :
    ∀ x : Fin 2 → ℝ, (0 < x 0 ∧ x 0 < (N:ℝ) ∧ Y < x 1) →
      g (x+Pi.single 0 (N:ℝ)) = g x := by
  let U : Set (Fin 2 → ℝ) := {x | 0 < x 0 ∧ x 0 < (N:ℝ) ∧ Y < x 1}
  let S := spectralEllipticCoordinates ⁻¹' (Ioc 0 (N:ℝ) ×ˢ Ioi Y)
  have hS : MeasurableSet S :=
    (measurableSet_Ioc.prod measurableSet_Ioi).preimage spectralEllipticCoordinates.continuous.measurable
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt (continuous_apply 0) continuous_const).inter
      (isOpen_lt continuous_const (continuous_apply 1)))
  have hshift : Continuous (fun x : Fin 2 → ℝ => x+Pi.single 0 (N:ℝ)) :=
    continuous_id.add continuous_const
  have hmap : MapsTo (fun x : Fin 2 → ℝ => x+Pi.single 0 (N:ℝ)) U
      {x | 0 < x 0 ∧ x 0 < 2*(N:ℝ) ∧ Y < x 1} := by
    intro x hx
    change 0 < x 0+(N:ℝ) ∧ x 0+(N:ℝ) < 2*(N:ℝ) ∧ Y < x 1+0
    rw [add_zero]
    exact ⟨by linarith [hx.1,Nat.cast_nonneg (α := ℝ) N],by linarith [hx.2.1],hx.2.2⟩
  have hsub : U ⊆ {x | 0 < x 0 ∧ x 0 < 2*(N:ℝ) ∧ Y < x 1} := by
    intro x hx
    exact ⟨hx.1,by linarith [hx.2.1,Nat.cast_nonneg (α := ℝ) N],hx.2.2⟩
  have hUs : U ⊆ S := fun _ hx => ⟨⟨hx.1,hx.2.1.le⟩,hx.2.2⟩
  have hperiod := (spectralEllipticCoordinates_measurePreserving.restrict_preimage
    (measurableSet_Ioc.prod measurableSet_Ioi)).quasiMeasurePreserving.ae_eq_comp
      (gamma0CuspTwoCellCoordinateRestriction_shift_volume_ae N r Y hY f)
  have hperiod' : ∀ᵐ x ∂volume, x ∈ S →
      gamma0CuspTwoCellCoordinateRestriction N r Y hY f (x 0+N,x 1) =
        gamma0CuspTwoCellCoordinateRestriction N r Y hY f (spectralEllipticCoordinates x) :=
    (ae_restrict_iff' hS).mp hperiod
  have hgfshift := (measurePreserving_add_right (volume : Measure (Fin 2 → ℝ))
    (Pi.single 0 (N:ℝ))).quasiMeasurePreserving.ae hgf
  have hae : (fun x : Fin 2 → ℝ => g (x+Pi.single 0 (N:ℝ))) =ᵐ[volume.restrict U] g := by
    apply (ae_restrict_iff' hU.measurableSet).mpr
    filter_upwards [hgf,hgfshift,hperiod'] with x hx hxshift hper
    intro hxU
    rw [hxshift (hmap hxU),hx (hsub hxU)]
    apply congrArg L
    simpa [spectralEllipticCoordinates_apply,Pi.add_apply] using hper (hUs hxU)
  exact Measure.eqOn_open_of_ae_eq (μ := volume) hae hU
    (hg.comp hshift.continuousOn hmap) (hg.mono hsub)

end ArtinMatthews
