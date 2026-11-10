module

public import ArtinMatthews.SpectralCuspTwoCellOperator
public import ArtinMatthews.SpectralHorizontalPeriodPartition
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SpectralCuspSeparablePairingBase
public import ArtinMatthews.SpectralCuspSeparablePairingFixedHeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive hyperbolic Laplacian of the period-window test
pairs exactly with minus the second vertical derivative test. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff

 theorem cuspVerticalSquare_weight_continuous (η : ℝ → ℝ) (hη : Continuous η) :
    Continuous (fun y : ℝ => y ^ 2 * η y) :=
  (continuous_id.pow 2).mul hη

 theorem cuspVerticalSquare_weight_compact (η : ℝ → ℝ) (hcη : HasCompactSupport η) :
    HasCompactSupport (fun y : ℝ => y ^ 2 * η y) := by
  apply hcη.mono'
  intro y hy
  by_contra hout
  apply hy
  change y ^ 2 * η y = 0
  rw [image_eq_zero_of_notMem_tsupport hout, mul_zero]

 theorem cuspSeparable_laplacian_scalar_identity (a b c d y : ℝ) (z : ℂ) :
    (-(y ^ 2) * (a * b + c * d)) • z =
      -((a * (y ^ 2 * b)) • z) - (c * (y ^ 2 * d)) • z := by
  rw [← neg_smul, ← sub_smul]
  congr 1
  ring

 theorem cuspSeparable_laplacian_integral_eq (w : ℝ) {Y : ℝ} (hY : 0 < Y)
    (χ χ₂ η η₂ : ℝ → ℝ)
    (hχ : Continuous χ) (hχ₂ : Continuous χ₂) (hη : Continuous η) (hη₂ : Continuous η₂)
    (hcχ : HasCompactSupport χ) (hcχ₂ : HasCompactSupport χ₂)
    (hcη : HasCompactSupport η) (hcη₂ : HasCompactSupport η₂)
    (f : CuspStripL2 w Y) :
    (∫ p : ℝ × ℝ, (-(p.2 ^ 2) * (χ₂ p.1 * η p.2 + χ p.1 * η₂ p.2)) • f p
      ∂cuspStripMeasure w Y) =
      -(∫ p : ℝ × ℝ, (χ₂ p.1 * (p.2 ^ 2 * η p.2)) • f p ∂cuspStripMeasure w Y) -
        ∫ p : ℝ × ℝ, (χ p.1 * (p.2 ^ 2 * η₂ p.2)) • f p ∂cuspStripMeasure w Y := by
  have hx := cuspSeparable_mul_L2_integrable w hY χ₂ (fun y : ℝ => y ^ 2 * η y) hχ₂
    (cuspVerticalSquare_weight_continuous η hη) hcχ₂ (cuspVerticalSquare_weight_compact η hcη) f
  have hy := cuspSeparable_mul_L2_integrable w hY χ (fun y : ℝ => y ^ 2 * η₂ y) hχ
    (cuspVerticalSquare_weight_continuous η₂ hη₂) hcχ (cuspVerticalSquare_weight_compact η₂ hcη₂) f
  calc
    _ = ∫ p : ℝ × ℝ,
        -((χ₂ p.1 * (p.2 ^ 2 * η p.2)) • f p) -
          (χ p.1 * (p.2 ^ 2 * η₂ p.2)) • f p ∂cuspStripMeasure w Y := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p =>
        cuspSeparable_laplacian_scalar_identity (χ₂ p.1) (η p.2) (χ p.1) (η₂ p.2) p.2 (f p)
    _ = _ := by
      have hxn : Integrable (fun p : ℝ × ℝ => -((χ₂ p.1 * (p.2 ^ 2 * η p.2)) • f p))
          (cuspStripMeasure w Y) := hx.neg
      rw [integral_sub hxn hy, integral_neg]

 theorem cuspTwoCell_partition_sq_pairing {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (η : ℝ → ℝ) (hη : Continuous η) (hcη : HasCompactSupport η)
    (f : CuspStripL2 w Y) :
    (∫ p : ℝ × ℝ, (spectralHorizontalPartition w p.1 * (p.2 ^ 2 * η p.2)) •
      cuspTwoCellExtension hw.le Y f p ∂cuspStripMeasure (2 * w) Y) =
      w • ∫ y in Ioi Y, η y • ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint f) y := by
  rw [cuspTwoCell_partition_pairing hw hY _ (cuspVerticalSquare_weight_continuous η hη)
    (cuspVerticalSquare_weight_compact η hcη) f]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : y ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (hY.trans hy))
  rw [mul_div_cancel_left₀ _ hy0]

 theorem cuspTwoCell_partition_laplacian_pairing {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (f : CuspStripL2 w Y) :
    (∫ p : ℝ × ℝ,
      (-(p.2 ^ 2) *
        (deriv (deriv (spectralHorizontalPartition w)) p.1 * ρ p.2 +
          spectralHorizontalPartition w p.1 * deriv (deriv ρ) p.2)) •
        cuspTwoCellExtension hw.le Y f p ∂cuspStripMeasure (2 * w) Y) =
      -(w • ∫ y in Ioi Y, deriv (deriv ρ) y •
        ((cuspVerticalPullback w Y).toContinuousLinearMap.adjoint f) y) := by
  have hα := spectralHorizontalPartition_contDiff w
  have hα' := (contDiff_infty_iff_deriv.mp hα).2
  have hα'' := (contDiff_infty_iff_deriv.mp hα').2
  have hρ' := (contDiff_infty_iff_deriv.mp hρ).2
  have hρ'' := (contDiff_infty_iff_deriv.mp hρ').2
  rw [cuspSeparable_laplacian_integral_eq (2 * w) hY _ _ _ _
    hα.continuous hα''.continuous hρ.continuous hρ''.continuous
    (spectralHorizontalPartition_hasCompactSupport hw)
    (spectralHorizontalPartition_hasCompactSupport hw).deriv.deriv hcρ hcρ.deriv.deriv
    (cuspTwoCellExtension hw.le Y f)]
  rw [cuspTwoCell_partition_deriv2_pairing hw hY _
      (cuspVerticalSquare_weight_continuous ρ hρ.continuous) (cuspVerticalSquare_weight_compact ρ hcρ) f,
    cuspTwoCell_partition_sq_pairing hw hY _ hρ''.continuous hcρ.deriv.deriv f,
    neg_zero, zero_sub]

end
end ArtinMatthews
