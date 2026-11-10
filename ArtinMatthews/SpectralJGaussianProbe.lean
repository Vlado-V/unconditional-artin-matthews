module

public import ArtinMatthews.SpectralJGaussianFubini
public import ArtinMatthews.ShiftedVoronoiBesselLaplace
public import ArtinMatthews.SpectralGaussianUniqueness
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

def spectralJGaussianProbe (p x : ℝ) : ℂ :=
  (x : ℂ) * (Real.exp (-(p * x ^ 2)) : ℂ)

theorem spectralJGaussianProbe_continuous (p : ℝ) :
    Continuous (spectralJGaussianProbe p) := by
  unfold spectralJGaussianProbe
  fun_prop

theorem spectralJGaussianProbe_integrable (p : ℝ) (hp : 0 < p) :
    IntegrableOn (spectralJGaussianProbe p) (Ioi (0 : ℝ)) := by
  have he : IntegrableOn (fun u : ℝ => (Real.exp (-(p * u)) : ℂ))
      (Ioi (0 : ℝ)) := by
    have hr := integrableOn_exp_mul_Ioi (a := -p) (neg_neg_of_pos hp) 0
    simpa only [neg_mul] using! hr.ofReal
  have hs := (spectral_positive_square_integrable _).mp he
  apply (hs.const_mul (1 / 2 : ℂ)).congr
  filter_upwards with x
  rw [Complex.real_smul]
  unfold spectralJGaussianProbe
  push_cast
  ring

theorem spectralJGaussianProbe_transform (p w : ℝ) (hp : 0 < p) (hw : 0 ≤ w) :
    spectralJGaussianTransform (spectralJGaussianProbe p) w =
      ((1 / (2 * p) * Real.exp (-w / (8 * p)) : ℝ) : ℂ) := by
  have hs := spectral_gaussian_to_laplace_integral
    (fun x : ℝ => spectralJGaussianKernel x w) p
  have hl : (∫ u in Ioi (0 : ℝ), spectralJGaussianKernel (Real.sqrt u) w *
      Complex.exp (-(p * u : ℝ))) =
      ((1 / p * Real.exp (-(w / 8) / p) : ℝ) : ℂ) := by
    calc
      _ = ∫ u in Ioi (0 : ℝ), (Real.exp (-(p * u)) : ℂ) *
          Complex.besselJ 0 (2 * (Real.sqrt ((w / 8) * u) : ℂ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        dsimp only
        unfold spectralJGaussianKernel
        rw [Real.sq_sqrt hu.le, Complex.ofReal_exp]
        rw [show u / 8 * w = w / 8 * u by ring]
        push_cast
        ring
      _ = _ := integral_exp_mul_besselJ_zero_sqrt p (w / 8) hp (by positivity)
  have hr : (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) *
      (x : ℂ) * spectralJGaussianKernel x w) =
      spectralJGaussianTransform (spectralJGaussianProbe p) w := by
    apply integral_congr_ae
    filter_upwards with x
    unfold spectralJGaussianProbe
    rw [show -(p : ℂ) * (x : ℂ) ^ 2 = ((-(p * x ^ 2) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_exp]
    ring
  rw [hl, hr] at hs
  have he : -(w / 8) / p = -w / (8 * p) := by ring
  rw [he] at hs
  apply (mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num))
  calc
    _ = ((1 / p * Real.exp (-w / (8 * p)) : ℝ) : ℂ) := hs.symm
    _ = _ := by push_cast; field_simp <;> ring

end
end ArtinMatthews
