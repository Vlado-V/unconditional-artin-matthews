module

public import ArtinMatthews.SpectralCuspFourierODEHorizontal
public import ArtinMatthews.SpectralCuspFourierODEDifferentiation
public import ArtinMatthews.SpectralHyperbolicComplexGreen
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

/-! Exact horizontal Fourier projection of the genuine differential
Laplacian. All derivative contractions are the actual Fréchet derivatives. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace ArtinMatthews

theorem cuspHorizontalWeightedMean_interval (w : ℝ) (hw : 0 ≤ w)
    (χ : ℝ → ℂ) (G : ℝ × ℝ → ℂ) (y : ℝ) :
    cuspHorizontalWeightedMean w χ G y =
      (w : ℂ)⁻¹ * ∫ x in (0 : ℝ)..w, χ x * G (x, y) := by
  unfold cuspHorizontalWeightedMean cuspHorizontalMean
  rw [intervalIntegral.integral_of_le hw]

theorem spectralPlaneSecond_horizontal_deriv (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G)
    (p : ℝ × ℝ) :
    spectralPlaneSecond G 0 p = deriv (deriv (fun x => G (x, p.2))) p.1 := by
  have hd : ContDiff ℝ ∞ (fun p => fderiv ℝ G p (1, 0)) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_const
  unfold spectralPlaneSecond
  simp only [spectralPlaneDirection, Matrix.cons_val_zero]
  rw [← spectralPlanePartialX_eq_fderiv (hd.differentiable (by simp) p)]
  unfold spectralPlanePartialX
  have he : (fun t => fderiv ℝ G (t, p.2) (1, 0)) = deriv (fun x => G (x, p.2)) := by
    funext t
    exact (spectralPlanePartialX_eq_fderiv (hG.differentiable (by simp) (t, p.2))).symm
  rw [he]

theorem cuspFourierMean_second_horizontal (w : ℝ) (hw : 0 < w) (n : ℤ)
    (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (y : ℝ)
    (hp : Function.Periodic (fun x => G (x, y)) w) :
    cuspHorizontalWeightedMean w (cuspFourierPhase w n) (spectralPlaneSecond G 0) y =
      -(((cuspFourierFrequency w n : ℝ) : ℂ) ^ 2 *
        cuspHorizontalWeightedMean w (cuspFourierPhase w n) G y) := by
  rw [cuspHorizontalWeightedMean_interval w hw.le,
    cuspHorizontalWeightedMean_interval w hw.le]
  simp_rw [spectralPlaneSecond_horizontal_deriv G hG]
  rw [cuspFourier_integral_second_deriv w hw n (fun x => G (x, y))
    (hG.comp (contDiff_id.prodMk contDiff_const)) hp]
  ring

theorem cuspFourierMean_laplacian_projection (w : ℝ) (hw : 0 < w) (n : ℤ)
    (G : ℝ × ℝ → ℂ) (hG : ContDiff ℝ ∞ G) (y eigenvalue : ℝ)
    (hEq : ∀ x : ℝ, -(y ^ 2) • (spectralPlaneSecond G 0 (x, y) +
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
        intro x _
        dsimp only
        rw [hEq x]
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
