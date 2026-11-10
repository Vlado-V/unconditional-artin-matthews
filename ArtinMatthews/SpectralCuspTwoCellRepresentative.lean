module

public import ArtinMatthews.SpectralCuspTwoCellOperator
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Exact first- and translated-second-cell representatives of the completed
two-cell extension, and agreement with actual periodic input functions. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

theorem cuspStripMeasure_width_mono {w v : ℝ} (hwv : w ≤ v) (Y : ℝ) :
    cuspStripMeasure w Y ≤ cuspStripMeasure v Y :=
  Measure.prod_mono (Measure.restrict_mono_set _ (Ioc_subset_Ioc le_rfl hwv)) le_rfl

theorem cuspStripMeasure_first_mem (w Y : ℝ) :
    ∀ᵐ z ∂cuspStripMeasure w Y, z.1 ∈ Ioc 0 w :=
  (Measure.quasiMeasurePreserving_fst (μ := cuspHorizontalMeasure w)
    (ν := cuspVerticalMeasure Y)).ae (ae_restrict_mem measurableSet_Ioc)

theorem cuspTwoCellExtension_first_ae {w : ℝ} (hw : 0 ≤ w) (Y : ℝ) (f : CuspStripL2 w Y) :
    cuspTwoCellExtension hw Y f =ᵐ[cuspStripMeasure w Y] f := by
  have hf := (cuspTwoCellExtension_ae hw Y f).filter_mono
    (ae_mono (cuspStripMeasure_width_mono (by linarith : w ≤ 2 * w) Y))
  filter_upwards [hf, cuspStripMeasure_first_mem w Y] with z hz hx
  simpa only [spectralTwoCellCoordinateFold, spectralTwoCellFold_first hx.2, Prod.eta] using hz

theorem spectralTwoCellTranslate_up_preserving (w : ℝ) :
    MeasurePreserving (fun x : ℝ => x + w) (cuspHorizontalMeasure w)
      (volume.restrict (Ioc w (2 * w))) := by
  have ht := (measurePreserving_add_right (volume : Measure ℝ) w).restrict_preimage
    (s := Ioc w (2 * w)) measurableSet_Ioc
  have he : (fun x : ℝ => x + w) ⁻¹' Ioc w (2 * w) = Ioc 0 w := by
    ext x
    simp only [mem_preimage, mem_Ioc]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
  change MeasurePreserving (fun x : ℝ => x + w)
    (volume.restrict ((fun x : ℝ => x + w) ⁻¹' Ioc w (2 * w)))
    (volume.restrict (Ioc w (2 * w))) at ht
  rw [he] at ht
  exact ht

theorem cuspTwoCellExtension_second_ae {w : ℝ} (hw : 0 ≤ w) (Y : ℝ) (f : CuspStripL2 w Y) :
    (fun z : ℝ × ℝ => cuspTwoCellExtension hw Y f (z.1 + w, z.2))
      =ᵐ[cuspStripMeasure w Y] f := by
  have hm : (volume.restrict (Ioc w (2 * w))).prod (cuspVerticalMeasure Y) ≤
      cuspStripMeasure (2 * w) Y :=
    Measure.prod_mono (Measure.restrict_mono_set _ (Ioc_subset_Ioc hw le_rfl)) le_rfl
  have ht : MeasurePreserving (fun z : ℝ × ℝ => (z.1 + w, z.2))
      (cuspStripMeasure w Y)
      ((volume.restrict (Ioc w (2 * w))).prod (cuspVerticalMeasure Y)) :=
    (spectralTwoCellTranslate_up_preserving w).prod (MeasurePreserving.id _)
  have hf := ht.quasiMeasurePreserving.ae_eq_comp
    ((cuspTwoCellExtension_ae hw Y f).filter_mono (ae_mono hm))
  filter_upwards [hf, cuspStripMeasure_first_mem w Y] with z hz hx
  have hzpos : w < z.1 + w := by linarith [hx.1]
  simpa only [Function.comp_def, spectralTwoCellCoordinateFold,
    spectralTwoCellFold_second hzpos, add_sub_cancel_right, Prod.eta] using hz

theorem cuspTwoCellExtension_shift_ae {w : ℝ} (hw : 0 ≤ w) (Y : ℝ) (f : CuspStripL2 w Y) :
    (fun z : ℝ × ℝ => cuspTwoCellExtension hw Y f (z.1 + w, z.2))
      =ᵐ[cuspStripMeasure w Y] cuspTwoCellExtension hw Y f :=
  (cuspTwoCellExtension_second_ae hw Y f).trans (cuspTwoCellExtension_first_ae hw Y f).symm

theorem cuspTwoCellExtension_toLp_periodic {w : ℝ} (hw : 0 ≤ w) (Y : ℝ)
    (F : ℝ × ℝ → ℂ) (hF : MemLp F 2 (cuspStripMeasure w Y))
    (hF2 : MemLp F 2 (cuspStripMeasure (2 * w) Y))
    (hperiod : ∀ z : ℝ × ℝ, F (z.1 + w, z.2) = F z) :
    cuspTwoCellExtension hw Y (hF.toLp F) = hF2.toLp F := by
  have hf : hF.toLp F =ᵐ[(2 : ℝ≥0∞) • cuspStripMeasure w Y] F :=
    Measure.ae_smul_measure hF.coeFn_toLp 2
  have hp := (spectralTwoCellCoordinateFold_preserving hw Y).quasiMeasurePreserving.ae_eq_comp hf
  apply Lp.ext
  refine (cuspTwoCellExtension_ae hw Y _).trans (hp.trans ?_)
  filter_upwards [hF2.coeFn_toLp] with z hzLp
  rw [hzLp]
  change F (spectralTwoCellFold w z.1, z.2) = F z
  by_cases hz : z.1 ≤ w
  · simp [spectralTwoCellFold_first hz]
  · rw [spectralTwoCellFold_second (lt_of_not_ge hz)]
    have h := hperiod (z.1 - w, z.2)
    simpa only [sub_add_cancel, Prod.eta] using h.symm

end
end ArtinMatthews
