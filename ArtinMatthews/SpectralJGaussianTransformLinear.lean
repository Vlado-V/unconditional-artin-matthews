module

public import ArtinMatthews.SpectralJGaussianFubini
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

/-! Exact finite linearity on the original positive half-line. -/
namespace ArtinMatthews
open Set Filter MeasureTheory
open scoped BigOperators
noncomputable section

theorem spectralJGaussianTransform_integrand_integrable (f : ℝ → ℂ)
    (hf : IntegrableOn f (Ioi (0 : ℝ))) (w : ℝ) :
    IntegrableOn (fun x : ℝ => f x * spectralJGaussianKernel x w) (Ioi 0) := by
  obtain ⟨C, _, hb⟩ := spectralJGaussianKernel_bound
  have hk : Continuous (fun x : ℝ => spectralJGaussianKernel x w) :=
    spectralJGaussianKernel_continuous.curry_left (y := w)
  apply (hf.norm.mul_const C).mono'
    (hf.aestronglyMeasurable.mul hk.aestronglyMeasurable)
  filter_upwards with x
  change ‖f x * spectralJGaussianKernel x w‖ ≤ ‖f x‖ * C
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb x w) (norm_nonneg _)

theorem spectralJGaussianTransform_congr_Ioi {f g : ℝ → ℂ}
    (h : EqOn f g (Ioi (0 : ℝ))) :
    spectralJGaussianTransform f = spectralJGaussianTransform g := by
  funext w
  unfold spectralJGaussianTransform
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [h hx]

theorem spectralJGaussianTransform_const_mul (c : ℂ) (f : ℝ → ℂ) :
    spectralJGaussianTransform (fun x => c * f x) =
      fun w => c * spectralJGaussianTransform f w := by
  funext w
  unfold spectralJGaussianTransform
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  exact mul_assoc _ _ _

theorem spectralJGaussianTransform_add (f g : ℝ → ℂ)
    (hf : IntegrableOn f (Ioi (0 : ℝ))) (hg : IntegrableOn g (Ioi (0 : ℝ))) :
    spectralJGaussianTransform (fun x => f x + g x) =
      fun w => spectralJGaussianTransform f w + spectralJGaussianTransform g w := by
  funext w
  unfold spectralJGaussianTransform
  simp only [add_mul]
  exact integral_add (spectralJGaussianTransform_integrand_integrable f hf w)
    (spectralJGaussianTransform_integrand_integrable g hg w)

theorem spectralJGaussianTransform_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, IntegrableOn (f i) (Ioi (0 : ℝ))) :
    spectralJGaussianTransform (fun x => ∑ i ∈ s, f i x) =
      fun w => ∑ i ∈ s, spectralJGaussianTransform (f i) w := by
  funext w
  unfold spectralJGaussianTransform
  simp only [Finset.sum_mul]
  exact integral_finsetSum s (fun i hi => spectralJGaussianTransform_integrand_integrable (f i) (hf i hi) w)

end
end ArtinMatthews
