module

public import ArtinMatthews.SpectralHeatArithmeticKernel
public import ArtinMatthews.SpectralJRegularizedWeight
public import ArtinMatthews.SpectralWeylContourIntegrand
public import ArtinMatthews.SpectralBesselPositiveOrderBound
public import ArtinMatthews.SpectralHorizontalContour
public import ArtinMatthews.SpectralJRegularizedBaseBounds
public import ArtinMatthews.SpectralWeylContourShift
public import ArtinMatthews.SpectralWeylKLNormalization
public import ArtinMatthews.SpectralWeylThreeEighths
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

namespace ArtinMatthews

open Set MeasureTheory Complex
open scoped ContDiff
noncomputable section

theorem spectralJRegularizedContour_shift (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (L R X : ℝ) (hL : 0 ≤ L) (hR : 1 ≤ R) (hX : 0 < X) :
    (∫ t : ℝ, spectralWeylContourIntegrand (fun ν x => Complex.besselJ ν x)
      (spectralJRegularizedWeight f L) R X (t : ℂ)) =
      ∫ t : ℝ, spectralWeylContourIntegrand (fun ν x => Complex.besselJ ν x)
        (spectralJRegularizedWeight f L) R X ((t : ℂ) + ((3 / 8 : ℝ) : ℂ) * I) := by
  let cylinder := fun (ν : ℂ) (x : ℝ) => Complex.besselJ ν (x : ℂ)
  obtain ⟨B, hB, hbase⟩ := spectralJRegularizedBase_fixed_bound f hf hc hp L hL
  have hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X / 2) ^ ν.re * Real.exp (X ^ 2 / 4) / ‖Complex.Gamma (ν + 1)‖ :=
    fun X hX ν hν => spectral_besselJ_norm_le_exp_of_re_nonneg ν hν hX
  obtain ⟨C, _, hbound⟩ := spectralWeylContour_height_bound cylinder
    (spectralJRegularizedWeight f L) (spectralJRegularizedBase f L)
    (spectralJRegularizedWeight_factor f L) hCylinder hB hbase hR hX
  apply spectral_horizontal_integral_eq_of_heightWeight _ (by norm_num)
  · intro z hz0 hz1
    exact spectralWeylJContour_differentiableAt _ R hX hz0
      (spectralJRegularizedWeight_differentiableAt f hf.continuous hc hp L z (by
        rw [abs_of_nonneg hz0]
        linarith))
  · intro t y hy0 hy1
    exact hbound t y hy0 (le_trans hy1 (by norm_num))

theorem spectralJRegularizedContour_uniform_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ L R X t : ℝ, 0 ≤ L → 1 ≤ R → 0 < X →
      ‖spectralWeylContourIntegrand (fun ν x => Complex.besselJ ν x)
        (spectralJRegularizedWeight f L) R X ((t : ℂ) + ((3 / 8 : ℝ) : ℂ) * I)‖ ≤
        C * ((X / 2) ^ (3 / 4 : ℝ) * Real.exp (X ^ 2 / 4)) / (1 + t ^ 2) := by
  obtain ⟨B, hB, hbase⟩ := spectralJRegularizedBase_inner_uniform_bound f hf hc hp
  obtain ⟨G, hG, hGamma⟩ := spectral_weyl_gamma_pair_three_eighths_bound
  refine ⟨2 * B * Real.exp (25 / 32) * G, by positivity, ?_⟩
  intro L R X t hL hR hX
  have hnorm : ‖(t : ℂ) + ((3 / 8 : ℝ) : ℂ) * I‖ ≤ 1 + |t| := by
    calc
      _ ≤ ‖(t : ℂ)‖ + ‖((3 / 8 : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = |t| + 3 / 8 := by norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by linarith
  have hGauss := spectralWeylGaussian_norm_bound hR t (3 / 8) (by norm_num)
  have hpoint := spectralWeylContourIntegrand_norm_le
    (fun ν x => Complex.besselJ ν x) (spectralJRegularizedWeight f L)
    (spectralJRegularizedBase f L) R X t (3 / 8) hX (by norm_num)
    (spectralJRegularizedWeight_factor f L _)
    (fun ν hν => spectral_besselJ_norm_le_exp_of_re_nonneg ν hν hX)
  norm_num only [show (2 : ℝ) * (3 / 8) = 3 / 4 by norm_num] at hpoint
  have hbase' := hbase L hL t
  have hGamma' := hGamma t
  have hsquare : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith only [sq_abs t, sq_nonneg (|t| - 1)]
  have hu : 0 < 1 + t ^ 2 := by positivity
  calc
    _ ≤ ((1 + |t|) * (B / (1 + t ^ 2) ^ 2) * Real.exp (25 / 32)) *
        ((X / 2) ^ (3 / 4 : ℝ) * Real.exp (X ^ 2 / 4)) * (G * (1 + |t|)) := by
      apply hpoint.trans
      gcongr
    _ = (B * Real.exp (25 / 32) * G * ((X / 2) ^ (3 / 4 : ℝ) * Real.exp (X ^ 2 / 4))) *
        ((1 + |t|) ^ 2 / (1 + t ^ 2) ^ 2) := by ring
    _ ≤ (B * Real.exp (25 / 32) * G * ((X / 2) ^ (3 / 4 : ℝ) * Real.exp (X ^ 2 / 4))) *
        (2 * (1 + t ^ 2) / (1 + t ^ 2) ^ 2) := by gcongr
    _ = _ := by field_simp

theorem spectralJRegularizedHeatKernel_uniform_small (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (m n : ℤ) (hmn : 0 < m * n) (X₀ : ℝ) (hX₀ : 0 < X₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ L R X : ℝ, 0 ≤ L → 1 ≤ R → 0 < X → X ≤ X₀ →
      ‖spectralABLHeatKernel (spectralJRegularizedWeight f L) R m n X‖ ≤ C * X ^ (-1 / 4 : ℝ) := by
  obtain ⟨D, hD, hPoint⟩ := spectralJRegularizedContour_uniform_bound f hf hc hp
  let W := ∫ t : ℝ, SourcePhysical.sourceContourHeightWeight t
  have hW : 0 ≤ W := integral_nonneg fun t => SourcePhysical.sourceContourHeightWeight_nonneg t
  let A := D * W + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(4 / Real.pi) * A * Real.exp (X₀ ^ 2 / 4), by positivity, ?_⟩
  intro L R X hL hR hX hXX
  let H := spectralJRegularizedWeight f L
  let base := spectralJRegularizedBase f L
  let cylinder := fun (ν : ℂ) (x : ℝ) => Complex.besselJ ν (x : ℂ)
  have hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X / 2) ^ ν.re * Real.exp (X ^ 2 / 4) / ‖Complex.Gamma (ν + 1)‖ :=
    fun X hX ν hν => spectral_besselJ_norm_le_exp_of_re_nonneg ν hν hX
  obtain ⟨B, hB, hbase⟩ := spectralJRegularizedBase_fixed_bound f hf hc hp L hL
  have hhol : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 5 / 8 →
      DifferentiableAt ℂ (spectralWeylContourIntegrand cylinder H R X) z := by
    intro z hz0 hz1
    exact spectralWeylJContour_differentiableAt H R hX hz0
      (spectralJRegularizedWeight_differentiableAt f hf.continuous hc hp L z (by
        rw [abs_of_nonneg hz0]
        linarith))
  have hint := spectralWeylContour_integrable_line cylinder H base
    (spectralJRegularizedWeight_factor f L) hCylinder hB hbase hR hX hhol (y := 0)
    (by norm_num) (by norm_num)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hint
  have hInt :
      ‖∫ t : ℝ, spectralWeylContourIntegrand cylinder H R X (t : ℂ)‖ ≤
        A * ((X / 2) ^ (3 / 4 : ℝ) * Real.exp (X ^ 2 / 4)) := by
    rw [spectralJRegularizedContour_shift f hf hc hp L R X hL hR hX]
    let P := (X / 2) ^ (3 / 4 : ℝ) * Real.exp (X ^ 2 / 4)
    have hP : 0 ≤ P := by dsimp [P]; positivity
    calc
      _ ≤ ∫ t : ℝ, (D * P) * SourcePhysical.sourceContourHeightWeight t := by
        apply norm_integral_le_of_norm_le
          (SourcePhysical.sourceContourHeightWeight_integrable.const_mul (D * P))
        exact ae_of_all _ fun t => by
          simpa only [P, SourcePhysical.sourceContourHeightWeight, div_eq_mul_inv] using
            hPoint L R X t hL hR hX
      _ = D * P * W := by rw [integral_const_mul]
      _ ≤ A * P := by dsimp [A]; nlinarith
  have hN : ‖-(4 * I) / ((Real.pi : ℂ) * (X : ℂ))‖ = (4 / Real.pi) / X := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX, abs_of_pos Real.pi_pos, div_div]
  have hpow : (X / 2) ^ (3 / 4 : ℝ) ≤ X ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have hexp : Real.exp (X ^ 2 / 4) ≤ Real.exp (X₀ ^ 2 / 4) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hxp : X ^ (3 / 4 : ℝ) / X = X ^ (-1 / 4 : ℝ) := by
    rw [show (3 / 4 : ℝ) = -1 / 4 + 1 by norm_num, Real.rpow_add hX, Real.rpow_one]
    exact mul_div_cancel_right₀ _ hX.ne'
  simp only [spectralABLHeatKernel, spectralWeylIntegerSignMultiplier, ite_eq_left hmn]
  rw [(spectralWeylJGaussian_eq_contour H (spectralJRegularizedWeight_even f L) R hX hint).2,
    norm_mul, hN]
  calc
    _ ≤ ((4 / Real.pi) / X) * (A * ((X / 2) ^ (3 / 4 : ℝ) * Real.exp (X ^ 2 / 4))) := by
      gcongr
    _ ≤ ((4 / Real.pi) / X) * (A * (X ^ (3 / 4 : ℝ) * Real.exp (X₀ ^ 2 / 4))) := by
      gcongr
    _ = ((4 / Real.pi) * A * Real.exp (X₀ ^ 2 / 4)) * (X ^ (3 / 4 : ℝ) / X) := by ring
    _ = _ := by rw [hxp]

end
end ArtinMatthews
