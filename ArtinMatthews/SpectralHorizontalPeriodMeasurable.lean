module

public import ArtinMatthews.SpectralHorizontalPeriodPartition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable


set_option backward.privateInPublic true
@[expose] public section

/-! Horizontal period integration needs only two-cell integrability and an almost-everywhere
shift identity. In particular, the field itself need not be continuous. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section

/-- A continuous weight supported in the two horizontal cells gives an integrable product
with every field integrable on those cells. -/
theorem spectralHorizontal_weight_integrable {w : ℝ} {A : ℝ → ℝ} {H : ℝ → ℂ}
    (hA : Continuous A) (hsupp : tsupport A ⊆ Icc 0 (2 * w))
    (hH : IntegrableOn H (Icc 0 (2 * w))) :
    Integrable (fun x => A x • H x) := by
  apply (hH.continuousOn_smul hA.continuousOn isCompact_Icc).integrable_of_forall_notMem_eq_zero
  intro x hx
  have hz : A x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hsupp ht))
  simp [hz]

/-- Exact two-cell periodization for an almost-everywhere periodic, integrable field. -/
theorem spectralHorizontal_two_cell_integral {w : ℝ} (hw : 0 < w)
    {A : ℝ → ℝ} {H : ℝ → ℂ} (hA : Continuous A)
    (hsupp : tsupport A ⊆ Icc 0 (2 * w))
    (hH : IntegrableOn H (Icc 0 (2 * w)))
    (hperiod : (fun x => H (x + w)) =ᵐ[volume.restrict (Ioc 0 w)] H) :
    (∫ x, A x • H x) = ∫ x in 0..w, (A x + A (x + w)) • H x := by
  have hi := spectralHorizontal_weight_integrable hA hsupp hH
  have hHcell : IntervalIntegrable H volume 0 w := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hw.le).mpr
    exact hH.mono_set (Icc_subset_Icc le_rfl (by linarith))
  have hfirst : IntervalIntegrable (fun x => A x • H x) volume 0 w :=
    hi.intervalIntegrable
  have hshift : IntervalIntegrable (fun x => A (x + w) • H x) volume 0 w :=
    hHcell.continuousOn_smul (hA.comp (continuous_id.add_const w)).continuousOn
  have hfull : (∫ x, A x • H x) = ∫ x in 0..2 * w, A x • H x := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : A x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hsupp ht))
    simp [hz]
  have hsecond : (∫ x in w..2 * w, A x • H x) =
      ∫ x in 0..w, A (x + w) • H x := by
    calc
      _ = ∫ x in 0..w, A (x + w) • H (x + w) := by
        simpa only [zero_add, ← two_mul] using
          (intervalIntegral.integral_comp_add_right (f := fun x => A x • H x)
            (a := 0) (b := w) w).symm
      _ = _ := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le hw.le]
        filter_upwards [hperiod] with x hx
        rw [hx]
  rw [hfull, ← intervalIntegral.integral_add_adjacent_intervals hfirst hi.intervalIntegrable,
    hsecond, ← intervalIntegral.integral_add hfirst hshift]
  apply intervalIntegral.integral_congr
  intro x _
  exact (add_smul (A x) (A (x + w)) (H x)).symm

/-- A constant periodized weight acts by its scalar on the one-period integral. -/
theorem spectralHorizontal_weighted_period_integral {w c : ℝ} (hw : 0 < w)
    {A : ℝ → ℝ} {H : ℝ → ℂ} (hA : Continuous A)
    (hsupp : tsupport A ⊆ Icc 0 (2 * w))
    (hH : IntegrableOn H (Icc 0 (2 * w)))
    (hperiod : (fun x => H (x + w)) =ᵐ[volume.restrict (Ioc 0 w)] H)
    (hpartition : ∀ x ∈ Ioo 0 w, A x + A (x + w) = c) :
    (∫ x, A x • H x) = c • ∫ x in 0..w, H x := by
  rw [spectralHorizontal_two_cell_integral hw hA hsupp hH hperiod]
  calc
    _ = ∫ x in 0..w, c • H x := by
      apply intervalIntegral.integral_congr_Ioo_of_le hw.le
      intro x hx
      change (A x + A (x + w)) • H x = c • H x
      rw [hpartition x hx]
    _ = _ := intervalIntegral.integral_smul c H

/-- The actual compact smooth partition extracts one period of any two-cell integrable field. -/
theorem spectralHorizontalPartition_integral {w : ℝ} (hw : 0 < w) {H : ℝ → ℂ}
    (hH : IntegrableOn H (Icc 0 (2 * w)))
    (hperiod : (fun x => H (x + w)) =ᵐ[volume.restrict (Ioc 0 w)] H) :
    (∫ x, spectralHorizontalPartition w x • H x) = ∫ x in 0..w, H x := by
  simpa using spectralHorizontal_weighted_period_integral (c := 1) hw
    (spectralHorizontalPartition_contDiff w).continuous
    (spectralHorizontalPartition_tsupport hw) hH hperiod
    (fun x hx => spectralHorizontalPartition_add_shift hw ⟨hx.1.le, hx.2.le⟩)

/-- The first derivative contributes no period integral, without any derivative of the field. -/
theorem spectralHorizontalPartition_deriv_integral {w : ℝ} (hw : 0 < w) {H : ℝ → ℂ}
    (hH : IntegrableOn H (Icc 0 (2 * w)))
    (hperiod : (fun x => H (x + w)) =ᵐ[volume.restrict (Ioc 0 w)] H) :
    (∫ x, deriv (spectralHorizontalPartition w) x • H x) = 0 := by
  have hd := (contDiff_infty_iff_deriv.mp (spectralHorizontalPartition_contDiff w)).2
  simpa using spectralHorizontal_weighted_period_integral (c := 0) hw hd.continuous
    (tsupport_deriv_subset.trans (spectralHorizontalPartition_tsupport hw)) hH hperiod
    (fun _ hx => spectralHorizontalPartition_deriv_add_shift hw hx)

/-- The second derivative also contributes no period integral for the actual measurable field. -/
theorem spectralHorizontalPartition_deriv2_integral {w : ℝ} (hw : 0 < w) {H : ℝ → ℂ}
    (hH : IntegrableOn H (Icc 0 (2 * w)))
    (hperiod : (fun x => H (x + w)) =ᵐ[volume.restrict (Ioc 0 w)] H) :
    (∫ x, deriv (deriv (spectralHorizontalPartition w)) x • H x) = 0 := by
  have hd := (contDiff_infty_iff_deriv.mp (spectralHorizontalPartition_contDiff w)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  simpa using spectralHorizontal_weighted_period_integral (c := 0) hw hdd.continuous
    (tsupport_deriv_subset.trans
      (tsupport_deriv_subset.trans (spectralHorizontalPartition_tsupport hw))) hH hperiod
    (fun _ hx => spectralHorizontalPartition_deriv2_add_shift hw hx)

/-- Local integrability and global almost-everywhere periodicity imply the same exact identity. -/
theorem spectralHorizontalPartition_integral_of_locallyIntegrable {w : ℝ} (hw : 0 < w)
    {H : ℝ → ℂ} (hH : LocallyIntegrable H volume)
    (hperiod : (fun x => H (x + w)) =ᵐ[volume] H) :
    (∫ x, spectralHorizontalPartition w x • H x) = ∫ x in 0..w, H x :=
  spectralHorizontalPartition_integral hw (hH.integrableOn_isCompact isCompact_Icc)
    (ae_restrict_of_ae hperiod)

end
end ArtinMatthews
