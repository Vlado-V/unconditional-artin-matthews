module

public import ArtinMatthews.SpectralJGaussianTail
public import ArtinMatthews.SpectralJGaussianTailFubini
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Literal KL integration of the Gaussian tail, with a bound in the
one-step radial decay constant. -/

namespace ArtinMatthews

open MeasureTheory Set OAI.CubicEisenstein

noncomputable section

private theorem tailKernel_eq_laplace (t y w : ℝ) (hy : 0 < y) :
    spectralJTailKernel t y w =
      ((Real.sqrt y * Real.exp y / y : ℝ) : ℂ) *
        schlafliBesselK ((t : ℂ) * Complex.I) y * (Real.exp (-(y * w)) : ℂ) := by
  have hpow : Real.sqrt y / y = y ^ (-(1 / 2) : ℝ) := by
    calc
      _ = y ^ (1 / 2 : ℝ) / y ^ (1 : ℝ) := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = y ^ ((1 / 2 : ℝ) - 1) := (Real.rpow_sub hy _ _).symm
      _ = _ := by norm_num
  have hr : Real.exp (-((w - 1) * y)) * y ^ (-(1 / 2) : ℝ) =
      (Real.sqrt y * Real.exp y / y) * Real.exp (-(y * w)) := by
    rw [← hpow, show -((w - 1) * y) = y + -(y * w) by ring, Real.exp_add]
    ring
  rw [spectralJTailKernel, hr, Complex.ofReal_mul]
  ring

theorem spectralJGaussianTail_KLKernel_eq_inner (F : ℝ → ℂ) (t : ℝ) {y : ℝ} (hy : 0 < y) :
    spectralJGaussianTail F y * schlafliBesselK ((t : ℂ) * Complex.I) y / (y : ℂ) =
      ∫ w in Ioi (2 : ℝ), spectralJTailKernel t y w * F w := by
  rw [spectralJGaussianTail, ite_eq_left hy]
  calc
    _ = (((Real.sqrt y * Real.exp y / y : ℝ) : ℂ) *
        schlafliBesselK ((t : ℂ) * Complex.I) y) *
        (∫ w in Ioi (2 : ℝ), (Real.exp (-(y * w)) : ℂ) * F w) := by
      push_cast
      ring
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _
      dsimp only
      rw [tailKernel_eq_laplace t y w hy]
      ring

theorem spectralJGaussianTail_KLIntegral_integrable (F : ℝ → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (t : ℝ) :
    IntegrableOn (fun y : ℝ =>
      spectralJGaussianTail F y * schlafliBesselK ((t : ℂ) * Complex.I) y / (y : ℂ)) (Ioi 0) := by
  apply (spectralJTailKernel_pair_integrable F hF B hB hbound t).integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (spectralJGaussianTail_KLKernel_eq_inner F t hy).symm

theorem spectralJGaussianTail_KLIntegral_eq (F : ℝ → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (t : ℝ) :
    (∫ y in Ioi (0 : ℝ),
      spectralJGaussianTail F y * schlafliBesselK ((t : ℂ) * Complex.I) y / (y : ℂ)) =
      ∫ w in Ioi (2 : ℝ), F w * (∫ y in Ioi (0 : ℝ), spectralJTailKernel t y w) := by
  calc
    _ = ∫ y in Ioi (0 : ℝ), ∫ w in Ioi (2 : ℝ), spectralJTailKernel t y w * F w :=
      setIntegral_congr_fun measurableSet_Ioi (fun _ hy => spectralJGaussianTail_KLKernel_eq_inner F t hy)
    _ = ∫ w in Ioi (2 : ℝ), ∫ y in Ioi (0 : ℝ), spectralJTailKernel t y w * F w :=
      spectralJTailKernel_integral_swap F hF B hB hbound t
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro w _
      dsimp only
      rw [integral_mul_const, mul_comm]

theorem spectralJGaussianTail_KLIntegral_norm_le (F : ℝ → ℂ) (hF : Measurable F)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w : ℝ, 2 < w → ‖F w‖ ≤ B / w) (t : ℝ) :
    ‖∫ y in Ioi (0 : ℝ),
      spectralJGaussianTail F y * schlafliBesselK ((t : ℂ) * Complex.I) y / (y : ℂ)‖ ≤
      4 * spectralJTailKZeroMellinMass * B := by
  obtain ⟨hp, hb⟩ := spectralJTailKernel_pair_integrable_and_bound F hF B hB hbound t
  have he : (∫ y in Ioi (0 : ℝ),
      spectralJGaussianTail F y * schlafliBesselK ((t : ℂ) * Complex.I) y / (y : ℂ)) =
      ∫ y in Ioi (0 : ℝ), ∫ w in Ioi (2 : ℝ), spectralJTailKernel t y w * F w :=
    setIntegral_congr_fun measurableSet_Ioi (fun _ hy => spectralJGaussianTail_KLKernel_eq_inner F t hy)
  rw [he]
  calc
    _ ≤ ∫ y in Ioi (0 : ℝ), ‖∫ w in Ioi (2 : ℝ), spectralJTailKernel t y w * F w‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi (0 : ℝ), ∫ w in Ioi (2 : ℝ), ‖spectralJTailKernel t y w * F w‖ := by
      apply integral_mono_ae hp.integral_prod_left.norm hp.integral_norm_prod_left
      filter_upwards with y
      exact norm_integral_le_integral_norm _
    _ ≤ _ := hb

end
end ArtinMatthews
