module

public import ArtinMatthews.SpectralCuspFourierODEDifferentiation
public import ArtinMatthews.SpectralCuspFourierODEHorizontal
public import ArtinMatthews.SpectralHyperbolicComplexGreen
public import ArtinMatthews.SpectralCuspFourierODEProjection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Local Fourier calculus: only matching endpoint jets on one period are
needed for horizontal integration by parts. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace ArtinMatthews

theorem cuspFourier_integral_deriv_endpoints (w : ℝ) (hw : 0 < w) (n : ℤ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hend : f w = f 0) :
    (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * deriv f x) =
      (((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I) *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x) := by
  have hχ := cuspFourierPhase_contDiff w n
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => cuspFourierPhase_hasDerivAt w n x)
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
    ((hχ.continuous.mul continuous_const).intervalIntegrable 0 w)
    (hd.continuous.intervalIntegrable 0 w)
  rw [cuspFourierPhase_period w hw n, cuspFourierPhase_zero, one_mul, one_mul,
    hend, sub_self, zero_sub] at he
  have hfactor : (∫ x in (0 : ℝ)..w, (cuspFourierPhase w n x *
      (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I)) * f x) =
      (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I) *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hfactor] at he
  simpa only [neg_mul, neg_neg] using he

theorem cuspFourier_integral_second_deriv_endpoints (w : ℝ) (hw : 0 < w) (n : ℤ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hend : f w = f 0) (hdend : deriv f w = deriv f 0) :
    (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * deriv (deriv f) x) =
      -(((cuspFourierFrequency w n : ℝ) : ℂ) ^ 2 *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x)) := by
  rw [cuspFourier_integral_deriv_endpoints w hw n (deriv f)
    (contDiff_infty_iff_deriv.mp hf).2 hdend,
    cuspFourier_integral_deriv_endpoints w hw n f hf hend]
  calc
    _ = (((cuspFourierFrequency w n : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem cuspFourierMean_second_horizontal_endpoints (w : ℝ) (hw : 0 < w) (n : ℤ)
    (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (y : ℝ)
    (hend : G (w, y) = G (0, y))
    (hdend : deriv (fun x => G (x, y)) w = deriv (fun x => G (x, y)) 0) :
    cuspHorizontalWeightedMean w (cuspFourierPhase w n) (spectralPlaneSecond G 0) y =
      -(((cuspFourierFrequency w n : ℝ) : ℂ) ^ 2 *
        cuspHorizontalWeightedMean w (cuspFourierPhase w n) G y) := by
  rw [cuspHorizontalWeightedMean_interval w hw.le,
    cuspHorizontalWeightedMean_interval w hw.le]
  simp_rw [spectralPlaneSecond_horizontal_deriv G hG]
  rw [cuspFourier_integral_second_deriv_endpoints w hw n (fun x => G (x, y))
    (hG.comp (contDiff_id.prodMk contDiff_const)) hend hdend]
  ring

theorem cuspHorizontalWeightedMean_deriv_hasDerivAt (w : ℝ) (χ : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (y : ℝ) (hy : 0 < y) :
    HasDerivAt (deriv (cuspHorizontalWeightedMean w χ G))
      (cuspHorizontalWeightedMean w χ (spectralPlaneSecond G 1) y) y := by
  have hD : ContDiff ℝ ∞ (fun p => fderiv ℝ G p (0, 1)) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_const
  have hd := cuspHorizontalWeightedMean_hasDerivAt w hχ hD hy
  have he : (fun p => fderiv ℝ (fun q => fderiv ℝ G q (0, 1)) p (0, 1)) =
      spectralPlaneSecond G 1 := by
    funext p
    rfl
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hy] with t ht
  exact cuspHorizontalWeightedMean_deriv w hχ hG ht

theorem cuspHorizontalWeightedMean_second_deriv (w : ℝ) (χ : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (y : ℝ) (hy : 0 < y) :
    deriv (deriv (cuspHorizontalWeightedMean w χ G)) y =
      cuspHorizontalWeightedMean w χ (spectralPlaneSecond G 1) y :=
  (cuspHorizontalWeightedMean_deriv_hasDerivAt w χ hχ G hG y hy).deriv

theorem cuspFourierMean_laplacian_projection_on_cell (w : ℝ) (hw : 0 < w) (n : ℤ)
    (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (y eigenvalue : ℝ)
    (hEq : ∀ x ∈ uIcc (0 : ℝ) w, -(y ^ 2) • (spectralPlaneSecond G 0 (x, y) +
      spectralPlaneSecond G 1 (x, y)) = (eigenvalue : ℂ) * G (x, y)) :
    -(y ^ 2) •
      (cuspHorizontalWeightedMean w (cuspFourierPhase w n) (spectralPlaneSecond G 0) y +
        cuspHorizontalWeightedMean w (cuspFourierPhase w n) (spectralPlaneSecond G 1) y) =
      (eigenvalue : ℂ) * cuspHorizontalWeightedMean w (cuspFourierPhase w n) G y := by
  have hA : IntervalIntegrable
      (fun x => cuspFourierPhase w n x * spectralPlaneSecond G 0 (x, y)) volume 0 w :=
    ((cuspFourierPhase_contDiff w n).continuous.mul
      ((spectralPlaneSecond_contDiff G hG 0).continuous.comp
        (continuous_id.prodMk continuous_const))).intervalIntegrable 0 w
  have hB : IntervalIntegrable
      (fun x => cuspFourierPhase w n x * spectralPlaneSecond G 1 (x, y)) volume 0 w :=
    ((cuspFourierPhase_contDiff w n).continuous.mul
      ((spectralPlaneSecond_contDiff G hG 1).continuous.comp
        (continuous_id.prodMk continuous_const))).intervalIntegrable 0 w
  have he : -((y ^ 2 : ℝ) : ℂ) *
      ((∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * spectralPlaneSecond G 0 (x, y)) +
        ∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * spectralPlaneSecond G 1 (x, y)) =
      (eigenvalue : ℂ) * (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * G (x, y)) := by
    calc
      _ = ∫ x in (0 : ℝ)..w, cuspFourierPhase w n x *
          (-(y ^ 2) • (spectralPlaneSecond G 0 (x, y) + spectralPlaneSecond G 1 (x, y))) := by
        rw [← intervalIntegral.integral_add hA hB, ← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        simp only [Complex.real_smul, Complex.ofReal_neg]
        ring
      _ = ∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * ((eigenvalue : ℂ) * G (x, y)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp only
        rw [hEq x hx]
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        ring
  rw [cuspHorizontalWeightedMean_interval w hw.le,
    cuspHorizontalWeightedMean_interval w hw.le,
    cuspHorizontalWeightedMean_interval w hw.le]
  simp only [Complex.real_smul, Complex.ofReal_neg]
  calc
    _ = (w : ℂ)⁻¹ * (-((y ^ 2 : ℝ) : ℂ) *
      ((∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * spectralPlaneSecond G 0 (x, y)) +
        ∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * spectralPlaneSecond G 1 (x, y))) := by ring
    _ = _ := by rw [he]; ring

end ArtinMatthews
