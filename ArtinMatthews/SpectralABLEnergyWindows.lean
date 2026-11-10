module

public import ArtinMatthews.SpectralABLCorrectedWindows
public import ArtinMatthews.SpectralSourceEnergyParameter
public import ArtinMatthews.SpectralABLGaussianBound
public import ArtinMatthews.SpectralABLExceptionalBound
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

/-! Genuine bounded native energy multipliers for the literal source
windows. Division by cosh is performed through the regular Gamma factor
and includes both principal and complementary energies. -/

noncomputable section
open Set

namespace ArtinMatthews

theorem spectralABLRegularCorrected_real_bound (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) (t : ℝ) :
    ‖spectralABLRegularCorrected T Δ (t : ℂ)‖ ≤ spectralABLRegularBound T Δ := by
  rw [spectralABLRegularCorrected_real,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _)]
  exact (div_le_self (norm_nonneg _) (Real.one_le_cosh _)).trans
    (spectralABLRegularWindow_norm_le hT hΔ t)

theorem spectralABLExceptionalCorrected_real_bound (a : ℝ) {A : ℕ} (hA : 1 ≤ A) (t : ℝ) :
    ‖spectralABLExceptionalCorrected a A (t : ℂ)‖ ≤ spectralABLExceptionalBound A := by
  rw [spectralABLExceptionalCorrected_real,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.cosh_pos _)]
  exact (div_le_self (norm_nonneg _) (Real.one_le_cosh _)).trans
    (spectralABLExceptionalWindow_norm_le a hA t)

def spectralABLRegularEnergyTest (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) : SpectralEnergyTest :=
  spectralSourceEnergyTest (spectralABLRegularCorrected T Δ)
    (fun z hz => (spectralABLRegularCorrected_differentiableAt T Δ z (by linarith)).continuousAt)
    (spectralABLRegularBound T Δ) (spectralABLRegularCorrected_real_bound T Δ hT hΔ)

def spectralABLExceptionalEnergyTest (a : ℝ) (A : ℕ) (hA : 1 ≤ A) : SpectralEnergyTest :=
  spectralSourceEnergyTest (spectralABLExceptionalCorrected a A)
    (fun z hz => (spectralABLExceptionalCorrected_differentiableAt a hA z (by linarith)).continuousAt)
    (spectralABLExceptionalBound A) (spectralABLExceptionalCorrected_real_bound a hA)

theorem spectralABLRegularEnergyTest_apply (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) (l : Ici (0 : ℝ)) :
    spectralABLRegularEnergyTest T Δ hT hΔ l = spectralABLRegularCorrected T Δ (spectralSourceParameter l) := rfl

theorem spectralABLExceptionalEnergyTest_apply (a : ℝ) (A : ℕ) (hA : 1 ≤ A) (l : Ici (0 : ℝ)) :
    spectralABLExceptionalEnergyTest a A hA l = spectralABLExceptionalCorrected a A (spectralSourceParameter l) := rfl

theorem spectralABLRegularEnergyTest_continuous_symbol (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) (t : ℝ) :
    spectralContinuousTestSymbol (spectralABLRegularEnergyTest T Δ hT hΔ) t =
      spectralABLRegularWindow T Δ (t : ℂ)/(Real.cosh (Real.pi*t) : ℂ) := by
  rw [spectralABLRegularEnergyTest,spectralSourceEnergyTest_continuous_symbol
    _ _ _ _ (spectralABLRegularCorrected_even T Δ),spectralABLRegularCorrected_real]

theorem spectralABLExceptionalEnergyTest_continuous_symbol (a : ℝ) (A : ℕ) (hA : 1 ≤ A) (t : ℝ) :
    spectralContinuousTestSymbol (spectralABLExceptionalEnergyTest a A hA) t =
      spectralABLExceptionalWindow a A (t : ℂ)/(Real.cosh (Real.pi*t) : ℂ) := by
  rw [spectralABLExceptionalEnergyTest,spectralSourceEnergyTest_continuous_symbol
    _ _ _ _ (spectralABLExceptionalCorrected_even a A),spectralABLExceptionalCorrected_real]

def spectralABLRegularKuznetsovEnergyTest (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) : SpectralEnergyTest :=
  (1/4 : ℂ) • spectralABLRegularEnergyTest T Δ hT hΔ

def spectralABLExceptionalKuznetsovEnergyTest (a : ℝ) (A : ℕ) (hA : 1 ≤ A) : SpectralEnergyTest :=
  (1/4 : ℂ) • spectralABLExceptionalEnergyTest a A hA

theorem spectralSourceParameter_im_lt_half (l : ℝ) (hl : 0 < l) :
    |(spectralSourceParameter l).im| < 1/2 := by
  simp only [spectralSourceParameter,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,mul_one,Complex.I_re,mul_zero,zero_add,add_zero]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1/2)).mpr (by linarith)

theorem spectralSourceParameter_cosh_ne_zero (l : ℝ) (hl : 0 < l) :
    Complex.cosh ((Real.pi : ℂ)*spectralSourceParameter l) ≠ 0 := by
  intro hz
  have he := spectralABLCoshCancellation_mul_cosh (spectralSourceParameter l)
    (spectralSourceParameter_im_lt_half l hl)
  rw [hz,mul_zero,spectralSourceParameter_sq] at he
  have hl0 : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl.ne'
  apply hl0
  linear_combination -he

theorem spectralABLRegularEnergyTest_pos (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ)
    (l : Ici (0 : ℝ)) (hl : 0 < (l : ℝ)) :
    spectralABLRegularEnergyTest T Δ hT hΔ l =
      spectralABLRegularWindow T Δ (spectralSourceParameter l)/
        Complex.cosh ((Real.pi : ℂ)*spectralSourceParameter l) := by
  rw [spectralABLRegularEnergyTest_apply]
  exact (eq_div_iff (spectralSourceParameter_cosh_ne_zero l hl)).mpr
    (spectralABLRegularCorrected_mul_cosh T Δ _ (spectralSourceParameter_im_lt_half l hl))

theorem spectralABLExceptionalEnergyTest_pos (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (l : Ici (0 : ℝ)) (hl : 0 < (l : ℝ)) :
    spectralABLExceptionalEnergyTest a A hA l =
      spectralABLExceptionalWindow a A (spectralSourceParameter l)/
        Complex.cosh ((Real.pi : ℂ)*spectralSourceParameter l) := by
  rw [spectralABLExceptionalEnergyTest_apply]
  exact (eq_div_iff (spectralSourceParameter_cosh_ne_zero l hl)).mpr
    (spectralABLExceptionalCorrected_mul_cosh a A _ (spectralSourceParameter_im_lt_half l hl))

theorem spectralABLRegularEnergyTest_zero (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) :
    spectralABLRegularEnergyTest T Δ hT hΔ ⟨0,by norm_num⟩ =
      spectralABLRegularBase T Δ (Complex.I/2)/(Real.pi : ℂ) := by
  rw [spectralABLRegularEnergyTest_apply,spectralSourceParameter_zero,spectralABLRegularCorrected,
    spectralABLCoshCancellation_half_I]
  ring

theorem spectralABLExceptionalEnergyTest_zero (a : ℝ) (A : ℕ) (hA : 1 ≤ A) :
    spectralABLExceptionalEnergyTest a A hA ⟨0,by norm_num⟩ =
      spectralABLExceptionalBase a A (Complex.I/2)/(Real.pi : ℂ) := by
  rw [spectralABLExceptionalEnergyTest_apply,spectralSourceParameter_zero,spectralABLExceptionalCorrected,
    spectralABLCoshCancellation_half_I]
  ring

end ArtinMatthews
