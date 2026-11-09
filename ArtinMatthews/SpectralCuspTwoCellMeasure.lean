module

public import ArtinMatthews.CuspAverageProjectionOperator
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The literal two-cell folding map doubles the period-strip measure. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped ENNReal
noncomputable section

def spectralTwoCellFold (w x : ℝ) : ℝ := if x ≤ w then x else x - w

theorem spectralTwoCellFold_measurable (w : ℝ) : Measurable (spectralTwoCellFold w) := by
  unfold spectralTwoCellFold
  exact measurable_id.ite measurableSet_Iic (measurable_id.sub_const w)

theorem spectralTwoCellFold_first {w x : ℝ} (hx : x ≤ w) : spectralTwoCellFold w x = x :=
  ite_eq_left hx

theorem spectralTwoCellFold_second {w x : ℝ} (hx : w < x) : spectralTwoCellFold w x = x - w :=
  ite_eq_right hx.not_ge

theorem cuspHorizontalMeasure_two_cells {w : ℝ} (_hw : 0 ≤ w) :
    cuspHorizontalMeasure (2 * w) = cuspHorizontalMeasure w + volume.restrict (Ioc w (2 * w)) := by
  unfold cuspHorizontalMeasure
  have hu : Ioc (0 : ℝ) w ∪ Ioc w (2 * w) = Ioc 0 (2 * w) := by
    ext x
    simp only [mem_union, mem_Ioc]
    constructor
    · rintro (⟨h0, h1⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
    · rintro ⟨h0, h2⟩
      by_cases h1 : x ≤ w
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr ⟨lt_of_not_ge h1, h2⟩
  have hd : Disjoint (Ioc (0 : ℝ) w) (Ioc w (2 * w)) :=
    disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy.1)
  rw [← hu, Measure.restrict_union hd measurableSet_Ioc]

theorem spectralTwoCellTranslate_preserving (w : ℝ) :
    MeasurePreserving (fun x : ℝ => x - w) (volume.restrict (Ioc w (2 * w)))
      (cuspHorizontalMeasure w) := by
  have ht := (measurePreserving_add_right (volume : Measure ℝ) (-w)).restrict_preimage
    (s := Ioc 0 w) measurableSet_Ioc
  have he : (fun x : ℝ => x + -w) ⁻¹' Ioc 0 w = Ioc w (2 * w) := by
    ext x
    simp only [mem_preimage, mem_Ioc]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
  change MeasurePreserving (fun x : ℝ => x + -w)
    (volume.restrict ((fun x : ℝ => x + -w) ⁻¹' Ioc 0 w)) (volume.restrict (Ioc 0 w)) at ht
  rw [he] at ht
  exact ht

theorem spectralTwoCellFold_horizontal_map {w : ℝ} (hw : 0 ≤ w) :
    Measure.map (spectralTwoCellFold w) (cuspHorizontalMeasure (2 * w)) =
      (2 : ℝ≥0∞) • cuspHorizontalMeasure w := by
  have hfirst : Measure.map (spectralTwoCellFold w) (cuspHorizontalMeasure w) =
      cuspHorizontalMeasure w := by
    calc
      _ = Measure.map id (cuspHorizontalMeasure w) := Measure.map_congr (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact spectralTwoCellFold_first hx.2)
      _ = _ := Measure.map_id
  have hsecond : Measure.map (spectralTwoCellFold w) (volume.restrict (Ioc w (2 * w))) =
      cuspHorizontalMeasure w := by
    calc
      _ = Measure.map (fun x : ℝ => x - w) (volume.restrict (Ioc w (2 * w))) :=
        Measure.map_congr (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact spectralTwoCellFold_second hx.1)
      _ = _ := (spectralTwoCellTranslate_preserving w).map_eq
  rw [cuspHorizontalMeasure_two_cells hw, Measure.map_add _ _ (spectralTwoCellFold_measurable w),
    hfirst, hsecond, two_smul]

def spectralTwoCellCoordinateFold (w : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (spectralTwoCellFold w z.1, z.2)

theorem spectralTwoCellCoordinateFold_preserving {w : ℝ} (hw : 0 ≤ w) (Y : ℝ) :
    MeasurePreserving (spectralTwoCellCoordinateFold w) (cuspStripMeasure (2 * w) Y)
      ((2 : ℝ≥0∞) • cuspStripMeasure w Y) := by
  refine ⟨(spectralTwoCellFold_measurable w |>.comp measurable_fst).prodMk measurable_snd, ?_⟩
  change Measure.map (Prod.map (spectralTwoCellFold w) id)
    ((cuspHorizontalMeasure (2 * w)).prod (cuspVerticalMeasure Y)) = _
  rw [← Measure.map_prod_map _ _ (spectralTwoCellFold_measurable w) measurable_id,
    spectralTwoCellFold_horizontal_map hw, Measure.map_id, Measure.prod_smul_left]
  rfl

end
end ArtinMatthews
