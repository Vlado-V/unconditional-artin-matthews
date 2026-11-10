module

public import ArtinMatthews.SpectralCuspTwoCellOperator
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SpectralCuspVerticalTesting
public import ArtinMatthews.SpectralSeparableTestSeed
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.UniformSpace.Uniformizable


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine integrability and Fubini for separable compact tests against
arbitrary completed two-cell cusp fields. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff

 theorem cuspStripMeasure_le_smul_volume (w : ℝ) {Y : ℝ} (hY : 0 < Y) :
    cuspStripMeasure w Y ≤ ENNReal.ofReal (Y ^ (-2 : ℤ)) • (volume : Measure (ℝ × ℝ)) := by
  change (cuspHorizontalMeasure w).prod (cuspVerticalMeasure Y) ≤ _
  calc
    _ ≤ (volume : Measure ℝ).prod (ENNReal.ofReal (Y ^ (-2 : ℤ)) • volume) :=
      Measure.prod_mono Measure.restrict_le_self (cuspVerticalMeasure_le_smul_volume hY)
    _ = _ := by rw [Measure.prod_smul_right]; rfl

 theorem cuspSeparable_memLp (w : ℝ) {Y : ℝ} (hY : 0 < Y)
    (χ η : ℝ → ℝ) (hχ : Continuous χ) (hη : Continuous η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η) :
    MemLp (fun p : ℝ × ℝ => ((χ p.1 * η p.2 : ℝ) : ℂ)) 2 (cuspStripMeasure w Y) := by
  have hc : Continuous (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (η p.2 : ℂ)) :=
    (Complex.continuous_ofReal.comp (hχ.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp (hη.comp continuous_snd))
  have hs := spectralSeparablePlane_compact (fun x => (χ x : ℂ)) (fun y => (η y : ℂ))
    (hcχ.comp_left Complex.ofReal_zero) (hcη.comp_left Complex.ofReal_zero)
  have hp : MemLp (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (η p.2 : ℂ)) 2 volume :=
    hc.memLp_of_hasCompactSupport hs
  simpa only [Complex.ofReal_mul] using
    hp.of_measure_le_smul ENNReal.ofReal_ne_top (cuspStripMeasure_le_smul_volume w hY)

 theorem cuspSeparable_mul_L2_integrable (w : ℝ) {Y : ℝ} (hY : 0 < Y)
    (χ η : ℝ → ℝ) (hχ : Continuous χ) (hη : Continuous η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (f : CuspStripL2 w Y) :
    Integrable (fun p : ℝ × ℝ => (χ p.1 * η p.2) • f p) (cuspStripMeasure w Y) := by
  have H := (cuspSeparable_memLp w hY χ η hχ hη hcχ hcη).integrable_mul (Lp.memLp f)
  change Integrable (fun p : ℝ × ℝ => ((χ p.1 * η p.2 : ℝ) : ℂ) * f p)
    (cuspStripMeasure w Y) at H
  simpa only [Complex.real_smul] using H

 theorem cuspHorizontal_compact_weight_setIntegral (w : ℝ) (χ : ℝ → ℝ)
    (hχ : tsupport χ ⊆ Icc 0 (2 * w)) (H : ℝ → ℂ) :
    (∫ x in Ioc 0 (2 * w), χ x • H x) = ∫ x, χ x • H x := by
  rw [← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hzero := image_eq_zero_of_notMem_tsupport (fun ht => hx (hχ ht))
  rw [hzero, zero_smul]

 theorem cuspSeparable_twoCell_Fubini {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (χ η : ℝ → ℝ) (hχ : Continuous χ) (hη : Continuous η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hs : tsupport χ ⊆ Icc 0 (2 * w)) (f : CuspStripL2 w Y) :
    (∫ p : ℝ × ℝ, (χ p.1 * η p.2) • cuspTwoCellExtension hw.le Y f p
      ∂cuspStripMeasure (2 * w) Y) =
      ∫ y, η y • (∫ x, χ x • cuspTwoCellExtension hw.le Y f (x, y)) ∂cuspVerticalMeasure Y := by
  calc
    _ = ∫ y, (∫ x, (χ x * η y) • cuspTwoCellExtension hw.le Y f (x, y)
        ∂cuspHorizontalMeasure (2 * w)) ∂cuspVerticalMeasure Y :=
      integral_prod_symm _ (cuspSeparable_mul_L2_integrable (2 * w) hY χ η hχ hη hcχ hcη _)
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        change (∫ x in Ioc 0 (2 * w), (χ x * η y) • cuspTwoCellExtension hw.le Y f (x, y)) =
          η y • ∫ x, χ x • cuspTwoCellExtension hw.le Y f (x, y)
        rw [← integral_smul]
        simp_rw [smul_smul, mul_comm (η y)]
        simpa only [smul_smul] using cuspHorizontal_compact_weight_setIntegral w χ hs
          (fun x => η y • cuspTwoCellExtension hw.le Y f (x, y))


end
end ArtinMatthews
