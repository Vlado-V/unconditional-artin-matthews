module

public import ArtinMatthews.CuspAverageProjectionBase
public import ArtinMatthews.SpectralHorizontalPeriodPartition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import ArtinMatthews.CuspAverageProjectionOperator
public import ArtinMatthews.SpectralHorizontalPeriodMeasurable
public import Mathlib.MeasureTheory.Integral.Prod
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

/-! Fubini transfers two-cell periodization to actual integrable or L² fields.
No continuous representative, global periodic extension, or assumed fiber estimate is used. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section

/-- All three genuine weighted horizontal integrals and their integrability assertions. -/
def spectralHorizontalPeriodFiber (w : ℝ) (H : ℝ → ℂ) : Prop :=
  Integrable (fun x => spectralHorizontalPartition w x • H x) ∧
  Integrable (fun x => deriv (spectralHorizontalPartition w) x • H x) ∧
  Integrable (fun x => deriv (deriv (spectralHorizontalPartition w)) x • H x) ∧
  (∫ x, spectralHorizontalPartition w x • H x) = (∫ x in 0..w, H x) ∧
  (∫ x, deriv (spectralHorizontalPartition w) x • H x) = 0 ∧
  (∫ x, deriv (deriv (spectralHorizontalPartition w)) x • H x) = 0

/-- Simultaneous integrability and all three period identities for one measurable fiber. -/
theorem spectralHorizontalPeriodFiber_of_integrable {w : ℝ} (hw : 0 < w) {H : ℝ → ℂ}
    (hH : IntegrableOn H (Icc 0 (2 * w)))
    (hperiod : (fun x => H (x + w)) =ᵐ[volume.restrict (Ioc 0 w)] H) :
    spectralHorizontalPeriodFiber w H := by
  have hd := (contDiff_infty_iff_deriv.mp (spectralHorizontalPartition_contDiff w)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  exact ⟨spectralHorizontal_weight_integrable
      (spectralHorizontalPartition_contDiff w).continuous
      (spectralHorizontalPartition_tsupport hw) hH,
    spectralHorizontal_weight_integrable hd.continuous
      (tsupport_deriv_subset.trans (spectralHorizontalPartition_tsupport hw)) hH,
    spectralHorizontal_weight_integrable hdd.continuous
      (tsupport_deriv_subset.trans
        (tsupport_deriv_subset.trans (spectralHorizontalPartition_tsupport hw))) hH,
    spectralHorizontalPartition_integral hw hH hperiod,
    spectralHorizontalPartition_deriv_integral hw hH hperiod,
    spectralHorizontalPartition_deriv2_integral hw hH hperiod⟩

/-- Product-a.e. shift equality is enough: only the actual first and second cells are involved. -/
theorem spectralHorizontalPeriodFiber_ae_of_fiber_integrable {w : ℝ} (hw : 0 < w)
    {ν : Measure ℝ} [SFinite ν] {H : ℝ × ℝ → ℂ}
    (hH : ∀ᵐ y ∂ν, Integrable (fun x => H (x, y)) (volume.restrict (Ioc 0 (2 * w))))
    (hperiod : (fun p : ℝ × ℝ => H (p.1 + w, p.2))
      =ᵐ[(volume.restrict (Ioc 0 w)).prod ν] H) :
    ∀ᵐ y ∂ν, spectralHorizontalPeriodFiber w (fun x => H (x, y)) := by
  have hs := (Measure.measurePreserving_swap (μ := ν)
    (ν := volume.restrict (Ioc 0 w))).quasiMeasurePreserving.ae_eq_comp hperiod
  have hp := Measure.ae_ae_of_ae_prod hs
  filter_upwards [hH, hp] with y hy hpy
  apply spectralHorizontalPeriodFiber_of_integrable hw
  · exact (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr hy
  · exact hpy

/-- Fubini version for a genuinely integrable two-cell field and any sigma-finite vertical measure. -/
theorem spectralHorizontalPeriodFiber_ae_of_integrable {w : ℝ} (hw : 0 < w)
    {ν : Measure ℝ} [SFinite ν] {H : ℝ × ℝ → ℂ}
    (hH : Integrable H ((volume.restrict (Ioc 0 (2 * w))).prod ν))
    (hperiod : (fun p : ℝ × ℝ => H (p.1 + w, p.2))
      =ᵐ[(volume.restrict (Ioc 0 w)).prod ν] H) :
    ∀ᵐ y ∂ν, spectralHorizontalPeriodFiber w (fun x => H (x, y)) :=
  spectralHorizontalPeriodFiber_ae_of_fiber_integrable hw hH.prod_left_ae hperiod

/-- Finite horizontal width turns each genuine L² fiber into an L¹ fiber.
The vertical measure need not have finite mass. -/
theorem spectralHorizontal_memLp_two_integrable_fibers (b : ℝ)
    {ν : Measure ℝ} [SFinite ν] {H : ℝ × ℝ → ℂ}
    (hH : MemLp H 2 ((volume.restrict (Ioc 0 b)).prod ν)) :
    ∀ᵐ y ∂ν, Integrable (fun x => H (x, y)) (volume.restrict (Ioc 0 b)) := by
  have hsq := (memLp_two_iff_integrable_sq_norm hH.aestronglyMeasurable).mp hH
  filter_upwards [hsq.prod_left_ae, hH.aestronglyMeasurable.prodMk_right] with y hy hmy
  exact ((memLp_two_iff_integrable_sq_norm hmy).mpr hy).integrable (by norm_num)

/-- Full a.e. period identities for a literal L² two-cell field, without a smoothness premise. -/
theorem spectralHorizontalPeriodFiber_ae_of_memLp {w : ℝ} (hw : 0 < w)
    {ν : Measure ℝ} [SFinite ν] {H : ℝ × ℝ → ℂ}
    (hH : MemLp H 2 ((volume.restrict (Ioc 0 (2 * w))).prod ν))
    (hperiod : (fun p : ℝ × ℝ => H (p.1 + w, p.2))
      =ᵐ[(volume.restrict (Ioc 0 w)).prod ν] H) :
    ∀ᵐ y ∂ν, spectralHorizontalPeriodFiber w (fun x => H (x, y)) :=
  spectralHorizontalPeriodFiber_ae_of_fiber_integrable hw
    (spectralHorizontal_memLp_two_integrable_fibers (2 * w) hH) hperiod

/-- The actual unnormalized hyperbolic strip measure has exactly the required product structure. -/
theorem spectralHorizontalPeriodFiber_ae_of_cusp_memLp {w Y : ℝ} (hw : 0 < w)
    {H : ℝ × ℝ → ℂ} (hH : MemLp H 2 (cuspStripMeasure (2 * w) Y))
    (hperiod : (fun p : ℝ × ℝ => H (p.1 + w, p.2)) =ᵐ[cuspStripMeasure w Y] H) :
    ∀ᵐ y ∂cuspVerticalMeasure Y,
      spectralHorizontalPeriodFiber w (fun x => H (x, y)) :=
  spectralHorizontalPeriodFiber_ae_of_memLp hw hH hperiod

/-- On positive heights the genuine hyperbolic vertical measure has the same null sets as
Lebesgue measure, since its literal density is positive there. -/
theorem spectralHorizontal_cuspVertical_ae_iff {Y : ℝ} (hY : 0 < Y) {P : ℝ → Prop} :
    (∀ᵐ y ∂cuspVerticalMeasure Y, P y) ↔ ∀ᵐ y ∂volume.restrict (Ioi Y), P y := by
  rw [cuspVerticalMeasure, ae_withDensity_iff (by fun_prop)]
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Ioi] with y hy hmem
    apply hy
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (zpow_pos (hY.trans hmem) _))
  · intro h
    filter_upwards [h] with y hy using fun _ => hy

/-- The actual hyperbolic L² conclusion also holds for Lebesgue-a.e. positive height. -/
theorem spectralHorizontalPeriodFiber_ae_volume_of_cusp_memLp {w Y : ℝ}
    (hw : 0 < w) (hY : 0 < Y) {H : ℝ × ℝ → ℂ}
    (hH : MemLp H 2 (cuspStripMeasure (2 * w) Y))
    (hperiod : (fun p : ℝ × ℝ => H (p.1 + w, p.2)) =ᵐ[cuspStripMeasure w Y] H) :
    ∀ᵐ y ∂volume.restrict (Ioi Y),
      spectralHorizontalPeriodFiber w (fun x => H (x, y)) :=
  (spectralHorizontal_cuspVertical_ae_iff hY).mp
    (spectralHorizontalPeriodFiber_ae_of_cusp_memLp hw hH hperiod)

end
end ArtinMatthews
