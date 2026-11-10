module

public import ArtinMatthews.SpectralMacdonaldCoordinates
public import ArtinMatthews.SpectralKLCoshExponential
public import ArtinMatthews.SpectralKLRealKernel
public import ArtinMatthews.SpectralKLCoshFourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Convolution
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! The actual convolution of two cosh exponentials evaluates to K0 at
the hyperbolic addition radius. This supplies an integrable kernel. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped Topology Convolution FourierTransform

namespace ArtinMatthews

theorem spectralKLCoshExponential_integral {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ, spectralKLCoshExponential x u) = 2*schlafliBesselK 0 x := by
  calc
    _ = ∫ u : ℝ, spectralKLogKernel 0 x u := by
      apply integral_congr_ae
      filter_upwards with u
      unfold spectralKLCoshExponential spectralKLogKernel
      congr 1
      push_cast
      ring
    _ = _ := by rw [schlafliBesselK_hyperbolic_integral 0 hx]; ring

theorem spectralMacdonald_exponential_product {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (w u : ℝ) :
    spectralKLCoshExponential x u*spectralKLCoshExponential y (w-u) =
      spectralKLCoshExponential (spectralMacdonaldRadius x y w) (u-spectralMacdonaldShift x y w) := by
  unfold spectralKLCoshExponential
  rw [← Complex.exp_add,← Complex.ofReal_add]
  congr 1
  congr 1
  have h := spectralMacdonald_cosh_shift hx hy w u
  linarith

theorem spectralMacdonald_convolution {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (w : ℝ) :
    (spectralKLCoshExponential x ⋆[ContinuousLinearMap.mul ℂ ℂ] spectralKLCoshExponential y) w =
      2*schlafliBesselK 0 (spectralMacdonaldRadius x y w) := by
  rw [convolution_def]
  change (∫ u : ℝ, spectralKLCoshExponential x u*spectralKLCoshExponential y (w-u)) = _
  simp_rw [spectralMacdonald_exponential_product hx hy w]
  rw [integral_sub_right_eq_self]
  exact spectralKLCoshExponential_integral (spectralMacdonaldRadius_pos hx hy w)

theorem spectralMacdonald_radius_kernel_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Integrable (fun w : ℝ => schlafliBesselK 0 (spectralMacdonaldRadius x y w)) := by
  have hc : Integrable (spectralKLCoshExponential x ⋆[ContinuousLinearMap.mul ℂ ℂ] spectralKLCoshExponential y) :=
    (spectralKLCoshExponential_integrable hx).integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ)
      (spectralKLCoshExponential_integrable hy)
  apply (hc.const_mul (1/2 : ℂ)).congr
  filter_upwards with w
  rw [spectralMacdonald_convolution hx hy w]
  ring

theorem spectralMacdonald_radius_fourier {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (ξ : ℝ) :
    𝓕 (fun w : ℝ => schlafliBesselK 0 (spectralMacdonaldRadius x y w)) ξ =
      2*(spectralKLRealKernel (2*Real.pi*ξ) x : ℂ)*(spectralKLRealKernel (2*Real.pi*ξ) y : ℂ) := by
  have h := Real.fourier_mul_convolution_eq (spectralKLCoshExponential_integrable hx)
    (spectralKLCoshExponential_integrable hy) ξ
  have heq : (spectralKLCoshExponential x ⋆[ContinuousLinearMap.mul ℂ ℂ] spectralKLCoshExponential y) =
      (fun w : ℝ => 2*schlafliBesselK 0 (spectralMacdonaldRadius x y w)) :=
    funext (spectralMacdonald_convolution hx hy)
  have hlin : 𝓕 (fun w : ℝ => 2*schlafliBesselK 0 (spectralMacdonaldRadius x y w)) ξ =
      2*𝓕 (fun w : ℝ => schlafliBesselK 0 (spectralMacdonaldRadius x y w)) ξ := by
    rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with w
    simp only [smul_eq_mul]
    ring
  rw [heq,hlin,spectralKLCoshExponential_fourier hx,spectralKLCoshExponential_fourier hy] at h
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  calc
    _ = (2*(spectralKLRealKernel (2*Real.pi*ξ) x : ℂ))*(2*(spectralKLRealKernel (2*Real.pi*ξ) y : ℂ)) := h
    _ = _ := by ring

end ArtinMatthews
