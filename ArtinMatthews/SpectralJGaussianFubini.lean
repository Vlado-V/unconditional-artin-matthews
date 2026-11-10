module

public import ArtinMatthews.SpectralJGaussianKernel
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

def spectralJGaussianTransform (f : ℝ → ℂ) (w : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), f x * spectralJGaussianKernel x w

theorem spectralJGaussianTransform_continuous (f : ℝ → ℂ)
    (hf : Continuous f) (hfi : IntegrableOn f (Ioi (0 : ℝ))) :
    Continuous (spectralJGaussianTransform f) := by
  obtain ⟨C, hC, hbound⟩ := spectralJGaussianKernel_bound
  change Continuous (fun w : ℝ => ∫ x in Ioi (0 : ℝ),
    f x * spectralJGaussianKernel x w)
  apply continuous_of_dominated
      (F := fun w x : ℝ => f x * spectralJGaussianKernel x w)
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (bound := fun x : ℝ => ‖f x‖ * C)
  · intro w
    have hk : Continuous (fun x : ℝ => spectralJGaussianKernel x w) :=
      spectralJGaussianKernel_continuous.curry_left (y := w)
    have hm : Continuous (fun x : ℝ => f x * spectralJGaussianKernel x w) :=
      Continuous.mul (f := f) (g := fun x : ℝ => spectralJGaussianKernel x w) hf hk
    exact hm.aestronglyMeasurable
  · intro w
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound x w) (norm_nonneg _)
  · exact hfi.norm.mul_const C
  · filter_upwards with x
    have hk : Continuous (fun w : ℝ => spectralJGaussianKernel x w) :=
      spectralJGaussianKernel_continuous.curry_right (x := x)
    exact Continuous.mul (f := fun _ : ℝ => f x)
      (g := fun w : ℝ => spectralJGaussianKernel x w) continuous_const hk

theorem spectralJGaussianTransform_bound (f : ℝ → ℂ)
    (hfi : IntegrableOn f (Ioi (0 : ℝ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℝ, ‖spectralJGaussianTransform f w‖ ≤ B := by
  obtain ⟨C, hC, hbound⟩ := spectralJGaussianKernel_bound
  refine ⟨(∫ x in Ioi (0 : ℝ), ‖f x‖) * C, ?_, ?_⟩
  · exact mul_nonneg (integral_nonneg fun _ => norm_nonneg _) hC.le
  · intro w
    unfold spectralJGaussianTransform
    calc
      _ ≤ ∫ x in Ioi (0 : ℝ), ‖f x‖ * C := by
        apply norm_integral_le_of_norm_le (hfi.norm.mul_const C)
        filter_upwards with x
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound x w) (norm_nonneg _)
      _ = _ := integral_mul_const C (fun x : ℝ => ‖f x‖)

theorem spectralJGaussianTransform_pair_integrable (f : ℝ → ℂ)
    (hf : Continuous f) (hfi : IntegrableOn f (Ioi (0 : ℝ)))
    (Y : ℝ) (hY : 0 < Y) :
    Integrable (fun p : ℝ × ℝ =>
      f p.1 * ((Real.exp (-(Y * p.2)) : ℝ) : ℂ) *
        spectralJGaussianKernel p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ := spectralJGaussianKernel_bound
  have he : IntegrableOn (fun w : ℝ => Real.exp (-(Y * w))) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -Y) (neg_neg_of_pos hY) 0)
  have hb := hfi.norm.mul_prod (he.const_mul C)
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      f p.1 * ((Real.exp (-(Y * p.2)) : ℝ) : ℂ) *
        spectralJGaussianKernel p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply Continuous.aestronglyMeasurable
    exact ((hf.comp continuous_fst).mul (by fun_prop)).mul
      spectralJGaussianKernel_continuous
  apply hb.mono' hm
  filter_upwards with p
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    ‖f p.1‖ * Real.exp (-(Y * p.2)) * ‖spectralJGaussianKernel p.1 p.2‖
      ≤ ‖f p.1‖ * Real.exp (-(Y * p.2)) * C :=
        mul_le_mul_of_nonneg_left (hbound _ _) (by positivity)
    _ = ‖f p.1‖ * (C * Real.exp (-(Y * p.2))) := by ring

theorem spectralJGaussianTransform_laplace (f : ℝ → ℂ)
    (hf : Continuous f) (hfi : IntegrableOn f (Ioi (0 : ℝ)))
    (Y : ℝ) (hY : 0 < Y) :
    (∫ w in Ioi (0 : ℝ), (Real.exp (-(Y * w)) : ℂ) *
      spectralJGaussianTransform f w) =
      ∫ x in Ioi (0 : ℝ), f x *
        ((1 / Y * Real.exp (-(x ^ 2 / 8) / Y) : ℝ) : ℂ) := by
  have hpair := spectralJGaussianTransform_pair_integrable f hf hfi Y hY
  calc
    _ = ∫ w in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ),
        f x * (Real.exp (-(Y * w)) : ℂ) * spectralJGaussianKernel x w := by
      apply integral_congr_ae
      filter_upwards with w
      rw [spectralJGaussianTransform, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = ∫ x in Ioi (0 : ℝ), ∫ w in Ioi (0 : ℝ),
        f x * (Real.exp (-(Y * w)) : ℂ) * spectralJGaussianKernel x w :=
      (integral_integral_swap hpair).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      simp_rw [mul_assoc]
      rw [integral_const_mul, spectralJGaussianKernel_laplace x Y hY]

end
end ArtinMatthews
