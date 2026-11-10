module

public import ArtinMatthews.SourceArchJacquetGaussian
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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

/-! An absolutely convergent Gaussian-Laplace representation of the
actual +1/6 archimedean Jacquet kernel. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory Set Filter
open ArtinMatthews.VaryingKummerAnalytic
noncomputable section

def sourceArchJacquetLaplace (r t : ℝ) (z : ℂ) : ℝ :=
  t ^ (1 / 3 : ℝ) * Real.exp (-(r ^ 2 * t)) * Real.exp (-t * ‖z‖ ^ 2)

theorem sourceArchJacquetLaplace_nonneg (r t : ℝ) (z : ℂ) (ht : 0 ≤ t) :
    0 ≤ sourceArchJacquetLaplace r t z := by
  unfold sourceArchJacquetLaplace
  positivity

theorem sourceArchJacquetLaplace_point_integral {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (∫ t in Ioi 0, sourceArchJacquetLaplace r t z) =
      Real.Gamma (4 / 3) * (r ^ 2 + ‖z‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
  have hb : 0 < r ^ 2 + ‖z‖ ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (sq_nonneg _)
  have he : (fun t => sourceArchJacquetLaplace r t z) =
      (fun t : ℝ => t ^ ((4 / 3 : ℝ) - 1) * Real.exp (-((r ^ 2 + ‖z‖ ^ 2) * t))) := by
    funext t
    unfold sourceArchJacquetLaplace
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    · norm_num
    · congr 1
      ring
  rw [he, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 4 / 3) hb,
    one_div, Real.inv_rpow hb.le, ← Real.rpow_neg hb.le, mul_comm]

theorem sourceArchJacquetLaplace_spatial_integrable (r : ℝ) {t : ℝ} (ht : 0 < t) :
    Integrable (sourceArchJacquetLaplace r t) sourceComplexTraceMeasure := by
  have hg := (sourceArchGaussian_integrable ht).re
  exact hg.const_mul (t ^ (1 / 3 : ℝ) * Real.exp (-(r ^ 2 * t)))

theorem sourceArchJacquetLaplace_spatial_integral (r : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ z : ℂ, sourceArchJacquetLaplace r t z ∂sourceComplexTraceMeasure) =
      (2 * Real.pi) * (t ^ (-(2 / 3 : ℝ)) * Real.exp (-(r ^ 2 * t))) := by
  unfold sourceArchJacquetLaplace
  rw [integral_const_mul, sourceArchGaussian_integral ht]
  have hp : t ^ (1 / 3 : ℝ) / t = t ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = t ^ (1 / 3 : ℝ) / t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ ((1 / 3 : ℝ) - 1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by norm_num
  calc
    _ = (2 * Real.pi) * ((t ^ (1 / 3 : ℝ) / t) * Real.exp (-(r ^ 2 * t))) := by ring
    _ = _ := by rw [hp]

theorem sourceArchJacquetLaplace_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (Function.uncurry (sourceArchJacquetLaplace r))
      ((volume.restrict (Ioi (0 : ℝ))).prod sourceComplexTraceMeasure) := by
  have : SigmaFinite sourceComplexTraceMeasure := by
    change SigmaFinite ((2 : NNReal) • (volume : Measure ℂ))
    infer_instance
  have hm : Measurable (Function.uncurry (sourceArchJacquetLaplace r)) := by
    unfold sourceArchJacquetLaplace Function.uncurry
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact sourceArchJacquetLaplace_spatial_integrable r ht
  · have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := -(2 / 3 : ℝ)) (p := (1 : ℝ)) (b := r ^ 2)
      (by norm_num) (by norm_num) (sq_pos_of_pos hr)
    have hi : IntegrableOn (fun t : ℝ => (2 * Real.pi) * (t ^ (-(2 / 3 : ℝ)) *
        Real.exp (-(r ^ 2 * t)))) (Ioi 0) := by
      simpa only [Real.rpow_one, neg_mul] using! hbase.const_mul (2 * Real.pi)
    refine hi.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have hnon (z : ℂ) : 0 ≤ sourceArchJacquetLaplace r t z :=
      sourceArchJacquetLaplace_nonneg r t z ht.le
    change (2 * Real.pi) * (t ^ (-(2 / 3 : ℝ)) * Real.exp (-(r ^ 2 * t))) =
      ∫ z : ℂ, ‖sourceArchJacquetLaplace r t z‖ ∂sourceComplexTraceMeasure
    simp_rw [Real.norm_of_nonneg (hnon _)]
    exact (sourceArchJacquetLaplace_spatial_integral r ht).symm

theorem sourceArchJacquetComplexLaplace_integrable {r : ℝ} (hr : 0 < r) :
    Integrable (fun p : ℝ × ℂ => (sourceArchJacquetLaplace r p.1 p.2 : ℂ) *
      sourceArchJacquetPhase p.2) ((volume.restrict (Ioi (0 : ℝ))).prod sourceComplexTraceMeasure) := by
  have hreal := (sourceArchJacquetLaplace_integrable hr).norm
  have hm : Measurable (fun p : ℝ × ℂ => (sourceArchJacquetLaplace r p.1 p.2 : ℂ) *
      sourceArchJacquetPhase p.2) := by
    unfold sourceArchJacquetLaplace sourceArchJacquetPhase
    fun_prop
  exact hreal.mono' hm.aestronglyMeasurable (Eventually.of_forall fun p => by
    rw [norm_mul, Complex.norm_real, sourceArchJacquetPhase_norm, mul_one]
    exact le_rfl)

end
end ArtinMatthews.SourceArchJacquet
