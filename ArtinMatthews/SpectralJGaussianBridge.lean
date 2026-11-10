module

public import ArtinMatthews.SpectralJGaussianFubini
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

theorem spectralJGaussianTransform_laplace_integrable (f : ℝ → ℂ)
    (hf : Continuous f) (hfi : IntegrableOn f (Ioi (0 : ℝ)))
    (Y : ℝ) (hY : 0 < Y) :
    IntegrableOn (fun w : ℝ => (Real.exp (-(Y * w)) : ℂ) *
      spectralJGaussianTransform f w) (Ioi (0 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := spectralJGaussianTransform_bound f hfi
  have he : IntegrableOn (fun w : ℝ => Real.exp (-(Y * w))) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -Y) (neg_neg_of_pos hY) 0)
  have hc : Continuous (fun w : ℝ => (Real.exp (-(Y * w)) : ℂ) *
      spectralJGaussianTransform f w) := by
    have hec : Continuous (fun w : ℝ => (Real.exp (-(Y * w)) : ℂ)) := by fun_prop
    exact hec.mul (spectralJGaussianTransform_continuous f hf hfi)
  apply (he.mul_const B).mono' hc.aestronglyMeasurable
  filter_upwards with w
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul_of_nonneg_left (hb w) (Real.exp_pos _).le

theorem spectralJGaussianTransform_gaussian (f : ℝ → ℂ)
    (hf : Continuous f) (hfi : IntegrableOn f (Ioi (0 : ℝ)))
    (p : ℝ) (hp : 0 < p) :
    (∫ w in Ioi (0 : ℝ), (Real.exp (-((1 / (8 * p)) * w)) : ℂ) *
      spectralJGaussianTransform f w) =
      ((8 * p : ℝ) : ℂ) *
        ∫ x in Ioi (0 : ℝ), f x * (Real.exp (-(p * x ^ 2)) : ℂ) := by
  rw [spectralJGaussianTransform_laplace f hf hfi _ (by positivity),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have he : -(x ^ 2 / 8) / (1 / (8 * p)) = -(p * x ^ 2) := by
    field_simp
    <;> ring
  rw [he]
  have hc : (1 : ℝ) / (1 / (8 * p)) = 8 * p := by field_simp
  rw [hc]
  push_cast
  ring

theorem spectralJGaussianTransform_laplace_split (f : ℝ → ℂ)
    (hf : Continuous f) (hfi : IntegrableOn f (Ioi (0 : ℝ)))
    (Y : ℝ) (hY : 0 < Y) :
    (2 : ℂ) * (∫ u in (0 : ℝ)..1, (Real.exp (-(2 * Y * u)) : ℂ) *
      spectralJGaussianTransform f (2 * u)) +
      (∫ w in Ioi (2 : ℝ), (Real.exp (-(Y * w)) : ℂ) *
        spectralJGaussianTransform f w) =
      ∫ x in Ioi (0 : ℝ), f x *
        ((1 / Y * Real.exp (-(x ^ 2 / 8) / Y) : ℝ) : ℂ) := by
  let H : ℝ → ℂ := fun w => (Real.exp (-(Y * w)) : ℂ) *
    spectralJGaussianTransform f w
  have hi : IntegrableOn H (Ioi (0 : ℝ)) :=
    spectralJGaussianTransform_laplace_integrable f hf hfi Y hY
  have hs := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 2)))
  have hc := intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := (1 : ℝ)) H (2 : ℝ)
  have hc' : (2 : ℂ) * (∫ u in (0 : ℝ)..1,
      (Real.exp (-(2 * Y * u)) : ℂ) * spectralJGaussianTransform f (2 * u)) =
      ∫ w in (0 : ℝ)..2, H w := by
    have he (u : ℝ) : Y * (2 * u) = 2 * Y * u := by ring
    simpa only [H, Complex.real_smul, Complex.ofReal_ofNat, mul_zero, mul_one, he] using! hc
  rw [hc']
  exact hs.trans (spectralJGaussianTransform_laplace f hf hfi Y hY)

end
end ArtinMatthews
