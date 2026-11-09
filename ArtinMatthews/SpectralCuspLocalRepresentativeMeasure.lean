module

public import ArtinMatthews.SpectralCuspLocalSmoothExtension
public import ArtinMatthews.SpectralCuspTwoCellHyperbolic


set_option backward.privateInPublic true
@[expose] public section

/-! Ordinary local almost-everywhere representatives on the open two-cell
strip represent the actual weighted strip L² class. Boundary lines are null. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace ArtinMatthews

theorem cuspStripMeasure_absolutelyContinuous_volume (w Y : ℝ) :
    cuspStripMeasure w Y ≪ (volume : Measure (ℝ × ℝ)) := by
  have hh : cuspHorizontalMeasure w ≪ (volume : Measure ℝ) :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hv : cuspVerticalMeasure Y ≪ (volume : Measure ℝ) :=
    (withDensity_absolutelyContinuous (volume.restrict (Ioi Y)) _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  exact hh.prod hv

theorem cuspStripMeasure_openTwoCell_ae (N Y : ℝ) (hY : 0 < Y) :
    ∀ᵐ p ∂cuspStripMeasure (2 * N) Y, p ∈ spectralOpenTwoCell N Y := by
  have hxne : ∀ᵐ x ∂cuspHorizontalMeasure (2 * N), x ≠ 2 * N :=
    ae_restrict_of_ae (volume.ae_ne (2 * N))
  have hn := (Measure.quasiMeasurePreserving_fst (μ := cuspHorizontalMeasure (2 * N))
    (ν := cuspVerticalMeasure Y)).ae hxne
  filter_upwards [cuspStripMeasure_first_mem (2 * N) Y, cuspStripMeasure_height_mem hY (2 * N), hn]
    with p hx hy hne
  refine ⟨hx.1, ?_, hy⟩
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · exact hlt
  · exact (hne heq).elim

theorem cuspStripMeasure_local_ae (N Y : ℝ) (hY : 0 < Y)
    {P : (ℝ × ℝ) → Prop}
    (hP : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ spectralOpenTwoCell N Y → P p) :
    ∀ᵐ p ∂cuspStripMeasure (2 * N) Y, P p := by
  have h := hP.filter_mono (cuspStripMeasure_absolutelyContinuous_volume (2 * N) Y).ae_le
  filter_upwards [h, cuspStripMeasure_openTwoCell_ae N Y hY] with p hp hmem
  exact hp hmem

end ArtinMatthews
