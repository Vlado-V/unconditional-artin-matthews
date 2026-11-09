module

public import ArtinMatthews.SpectralGamma0FourierEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Exact compatibility of phase period N with the normalized two-cell
strip of width 2N.  The two-cell projection retains horizontal mass 2N. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal MatrixGroups

namespace ArtinMatthews

theorem cuspFourierPhase_add (T : ℝ) (n : ℤ) (x y : ℝ) :
    cuspFourierPhase T n (x + y) = cuspFourierPhase T n x * cuspFourierPhase T n y := by
  unfold cuspFourierPhase
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

theorem cuspFourierPhase_periodic (T : ℝ) (hT : 0 < T) (n : ℤ) :
    Function.Periodic (cuspFourierPhase T n) T := by
  intro x
  rw [cuspFourierPhase_add, cuspFourierPhase_period T hT n, mul_one]

theorem cuspFourierPhase_fold (T : ℝ) (hT : 0 < T) (n : ℤ) (x : ℝ) :
    cuspFourierPhase T n (spectralTwoCellFold T x) = cuspFourierPhase T n x := by
  by_cases hx : x ≤ T
  · rw [spectralTwoCellFold_first hx]
  · rw [spectralTwoCellFold_second (lt_of_not_ge hx)]
    simpa only [sub_add_cancel] using (cuspFourierPhase_periodic T hT n (x - T)).symm

theorem cuspFourierMean_fold (w : ℝ) (hw : 0 < w) (n : ℤ) (F : ℝ × ℝ → ℂ) (y : ℝ)
    (hF : AEStronglyMeasurable (fun x => F (x, y)) (cuspHorizontalMeasure w)) :
    cuspHorizontalWeightedMean (2 * w) (cuspFourierPhase w n)
      (fun p => F (spectralTwoCellFold w p.1, p.2)) y =
        cuspHorizontalWeightedMean w (cuspFourierPhase w n) F y := by
  have hm : MeasurePreserving (spectralTwoCellFold w) (cuspHorizontalMeasure (2 * w))
      ((2 : ℝ≥0∞) • cuspHorizontalMeasure w) :=
    ⟨spectralTwoCellFold_measurable w, spectralTwoCellFold_horizontal_map hw.le⟩
  have hmeas : AEStronglyMeasurable (fun x => cuspFourierPhase w n x * F (x, y))
      ((2 : ℝ≥0∞) • cuspHorizontalMeasure w) :=
    (((cuspFourierPhase_contDiff w n).continuous.aestronglyMeasurable).mul hF).smul_measure
      (2 : ℝ≥0∞)
  have hmap : AEStronglyMeasurable (fun x => cuspFourierPhase w n x * F (x, y))
      (Measure.map (spectralTwoCellFold w) (cuspHorizontalMeasure (2 * w))) := by
    rw [hm.map_eq]
    exact hmeas
  have he := (integral_map hm.aemeasurable hmap).symm
  rw [hm.map_eq] at he
  simp only [cuspFourierPhase_fold w hw n] at he
  rw [integral_smul_measure] at he
  norm_num only [ENNReal.toReal_ofNat, Complex.real_smul] at he
  unfold cuspHorizontalWeightedMean cuspHorizontalMean
  change (((2 * w : ℝ) : ℂ)⁻¹ * ∫ x, cuspFourierPhase w n x *
    F (spectralTwoCellFold w x, y) ∂cuspHorizontalMeasure (2 * w)) = _
  rw [he]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hw.ne']
  rfl

theorem cuspFourierProjection_twoCell_ae (w Y : ℝ) (hw : 0 < w) (n : ℤ)
    (f : CuspStripL2 w Y) :
    cuspFourierProjection (2 * w) Y w n (cuspTwoCellExtension hw.le Y f)
      =ᵐ[cuspVerticalMeasure Y] cuspFourierProjection w Y w n f := by
  have he := cuspHorizontalMean_congr_ae (2 * w) Y (by
    filter_upwards [cuspTwoCellExtension_ae hw.le Y f] with p hp
    exact congrArg (fun z => cuspFourierPhase w n p.1 * z) hp)
  have hs := (Lp.aestronglyMeasurable f).prodMk_right
  refine (cuspFourierProjection_ae (2 * w) Y w (by positivity) n _).trans ?_
  refine (he.trans ?_).trans (cuspFourierProjection_ae w Y w hw n f).symm
  filter_upwards [hs] with y hy
  exact cuspFourierMean_fold w hw n f y hy

def gamma0CuspTwoCellFourierCoefficient (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) :
    Gamma0RegionL2 N →L[ℝ] CuspVerticalL2 (2 * (N : ℝ)) Y :=
  ((cuspFourierProjection (2 * (N : ℝ)) Y (N : ℝ) n).restrictScalars ℝ).comp
    (gamma0CuspTwoCellCoordinateRestriction N r Y hY)

theorem gamma0CuspTwoCellFourierCoefficient_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (f : Gamma0RegionL2 N) :
    gamma0CuspTwoCellFourierCoefficient N r Y hY n f =ᵐ[cuspVerticalMeasure Y]
      gamma0CuspFourierCoefficient N r Y hY n f := by
  exact cuspFourierProjection_twoCell_ae (N : ℝ) Y (Nat.cast_pos.mpr (NeZero.pos N)) n _

end ArtinMatthews
