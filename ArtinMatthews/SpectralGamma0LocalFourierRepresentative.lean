module

public import ArtinMatthews.SpectralCuspInteriorPeriodMeasure
public import ArtinMatthews.SpectralCuspLocalRepresentativeMeasure
public import ArtinMatthews.SpectralCuspFourierWeakIdentification


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical interior-period coefficient of an actual local two-cell
representative agrees with the completed Fourier projection and inherits
both required energy integrals. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem cuspInteriorFourierCoefficient_twoCell_ae (w Y : ℝ) (hw : 0 < w)
    (n : ℤ) (f : CuspStripL2 w Y) :
    cuspInteriorFourierCoefficient w n (cuspTwoCellExtension hw.le Y f)
      =ᵐ[cuspVerticalMeasure Y] cuspFourierProjection w Y w n f := by
  have he := cuspInteriorFourierCoefficient_congr_ae w Y hw n
    (cuspTwoCellExtension_ae hw.le Y f)
  have hs := (Lp.aestronglyMeasurable f).prodMk_right
  have hm : cuspInteriorFourierCoefficient w n
      (fun p => f (spectralTwoCellFold w p.1, p.2)) =ᵐ[cuspVerticalMeasure Y]
        cuspHorizontalWeightedMean w (cuspFourierPhase w n) f := by
    filter_upwards [hs] with y hy
    exact cuspInteriorFourierCoefficient_fold w hw n f y hy
  exact he.trans (hm.trans (cuspFourierProjection_ae w Y w hw n f).symm)

theorem gamma0CuspInteriorFourierCoefficient_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (f : Gamma0RegionL2 N) :
    cuspInteriorFourierCoefficient (N : ℝ) n (gamma0CuspTwoCellCoordinateRestriction N r Y hY f)
      =ᵐ[cuspVerticalMeasure Y] gamma0CuspFourierCoefficient N r Y hY n f := by
  exact cuspInteriorFourierCoefficient_twoCell_ae (N : ℝ) Y (Nat.cast_pos.mpr (NeZero.pos N)) n _

theorem gamma0CuspLocalFourierRepresentative_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (f : Gamma0RegionL2 N)
    (u : ℝ × ℝ → ℂ)
    (hu : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ spectralOpenTwoCell (N : ℝ) Y →
      u p = gamma0CuspTwoCellCoordinateRestriction N r Y hY f p) :
    gamma0CuspFourierCoefficient N r Y hY n f =ᵐ[volume.restrict (Ioi Y)]
      cuspInteriorFourierCoefficient (N : ℝ) n u := by
  have hup := cuspStripMeasure_local_ae (N : ℝ) Y hY hu
  have hc := cuspInteriorFourierCoefficient_congr_ae (N : ℝ) Y
    (Nat.cast_pos.mpr (NeZero.pos N)) n hup
  exact (spectralHorizontal_cuspVertical_ae_iff hY).mp
    ((gamma0CuspInteriorFourierCoefficient_ae N r Y hY n f).symm.trans hc.symm)

theorem gamma0CuspLocalFourierRepresentative_energy (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (v : gamma0EnergySpace N)
    (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell (N : ℝ) Y))
    (hrep : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ spectralOpenTwoCell (N : ℝ) Y →
      u p = gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0EnergyInclusion N v) p) :
    IntegrableOn (fun y => ‖cuspInteriorFourierCoefficient (N : ℝ) n u y‖ ^ 2 / y ^ 2) (Ioi Y) ∧
      IntegrableOn (fun y => ‖deriv (cuspInteriorFourierCoefficient (N : ℝ) n u) y‖ ^ 2) (Ioi Y) := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  exact gamma0CuspFourier_classical_integrable_energy N r Y hY n v
    (cuspInteriorFourierCoefficient (N : ℝ) n u) (deriv (cuspInteriorFourierCoefficient (N : ℝ) n u))
    (cuspInteriorFourierCoefficient_continuousOn (N : ℝ) Y hN hY.le n u hu)
    (cuspInteriorFourierCoefficient_deriv_continuousOn (N : ℝ) Y hN hY.le n u hu)
    (cuspInteriorFourierCoefficient_hasDerivAt (N : ℝ) Y hN hY.le n u hu)
    (gamma0CuspLocalFourierRepresentative_ae N r Y hY n (gamma0EnergyInclusion N v) u hrep)

theorem gamma0CuspLocalFourierRepresentative_deriv_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (v : gamma0EnergySpace N)
    (u : ℝ × ℝ → ℂ) (hu : ContDiffOn ℝ ∞ u (spectralOpenTwoCell (N : ℝ) Y))
    (hrep : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ spectralOpenTwoCell (N : ℝ) Y →
      u p = gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0EnergyInclusion N v) p) :
    gamma0CuspFourierDerivative N r Y hY n v =ᵐ[volume.restrict (Ioi Y)]
      deriv (cuspInteriorFourierCoefficient (N : ℝ) n u) := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  exact gamma0CuspFourierDerivative_ae_classical N r Y hY n v
    (cuspInteriorFourierCoefficient (N : ℝ) n u) (deriv (cuspInteriorFourierCoefficient (N : ℝ) n u))
    (cuspInteriorFourierCoefficient_continuousOn (N : ℝ) Y hN hY.le n u hu)
    (cuspInteriorFourierCoefficient_deriv_continuousOn (N : ℝ) Y hN hY.le n u hu)
    (cuspInteriorFourierCoefficient_hasDerivAt (N : ℝ) Y hN hY.le n u hu)
    (gamma0CuspLocalFourierRepresentative_ae N r Y hY n (gamma0EnergyInclusion N v) u hrep)

end ArtinMatthews
