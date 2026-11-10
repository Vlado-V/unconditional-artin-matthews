module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Absolute sum–integral interchange for Mellin inversion

This adapts the proved argument `CubicFirstMoment.smooth_mellin_series` in
OAI's `CubicMoment/Estimates/MellinSeries.lean`, retaining only its actual
inputs: integrability of the inverse Mellin datum and absolute convergence
of the coefficient series. It applies to both the source and Bessel weights.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff

namespace ArtinMatthews

/-- A Mellin inversion datum can be summed termwise against an absolutely
convergent norm Dirichlet series. This also proves convergence of the result. -/
theorem hasSum_mellinInv_scaled {ι : Type*} [Countable ι]
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (F : ℂ → ℂ) (σ : ℝ)
    (hF : Integrable (fun t : ℝ ↦ F ((σ : ℂ) + t * Complex.I)))
    (habs : Summable (fun i ↦ ‖a i‖ * (N i) ^ (-σ)))
    (Z : ℝ) (hZ : 0 < Z) :
    HasSum (fun i ↦ a i * mellinInv σ F (N i / Z))
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        F ((σ : ℂ) + t * Complex.I) * (Z : ℂ) ^ ((σ : ℂ) + t * Complex.I) *
          ∑' i, a i * (N i : ℂ) ^ (-((σ : ℂ) + t * Complex.I))) := by
  let s (t : ℝ) : ℂ := (σ : ℂ) + t * Complex.I
  let G (i : ι) (t : ℝ) : ℂ :=
    (a i * (N i : ℂ) ^ (-s t)) * ((Z : ℂ) ^ (s t) * F (s t))
  have hnorm (i : ι) (t : ℝ) : ‖G i t‖ =
      (‖a i‖ * (N i) ^ (-σ)) * Z ^ σ * ‖F (s t)‖ := by
    simp only [G, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hN i),
      Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    simp only [s, Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero]
    ring
  have hGi (i : ι) : Integrable (G i) := by
    have hs : Continuous s := by dsimp [s]; fun_prop
    have hNc : Continuous (fun t ↦ (N i : ℂ) ^ (-s t)) :=
      (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (hN i).ne'))).continuous.comp hs.neg
    have hZc : Continuous (fun t ↦ (Z : ℂ) ^ s t) :=
      (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).continuous.comp hs
    apply (hF.norm.const_mul ((‖a i‖ * (N i) ^ (-σ)) * Z ^ σ)).mono'
      ((continuous_const.mul hNc).aestronglyMeasurable.mul
        (hZc.aestronglyMeasurable.mul hF.aestronglyMeasurable))
    exact Eventually.of_forall (fun t ↦ (hnorm i t).le)
  have hsum : Summable (fun i ↦ ∫ t : ℝ, ‖G i t‖) := by
    have he (i : ι) : (∫ t : ℝ, ‖G i t‖) =
        (‖a i‖ * (N i) ^ (-σ)) * (Z ^ σ * ∫ t : ℝ, ‖F (s t)‖) := by
      simp_rw [hnorm]
      rw [integral_const_mul]
      ring
    simpa only [he] using habs.mul_right (Z ^ σ * ∫ t : ℝ, ‖F (s t)‖)
  have hi := (hasSum_integral_of_summable_integral_norm hGi hsum).mul_left
    (((1 / (2 * Real.pi) : ℝ) : ℂ))
  have hsingle (i : ι) : a i * mellinInv σ F (N i / Z) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) * ∫ t : ℝ, G i t := by
    unfold mellinInv
    simp only [RCLike.real_smul_eq_coe_mul]
    rw [← mul_assoc, mul_comm (a i), mul_assoc, ← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    have hscale : ((N i / Z : ℝ) : ℂ) ^ (-s t) =
        (Z : ℂ) ^ s t * (N i : ℂ) ^ (-s t) := by
      rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (hN i).le hZ.le,
        div_eq_mul_inv, Complex.cpow_neg (Z : ℂ), inv_inv, mul_comm]
    change a i * (((N i / Z : ℝ) : ℂ) ^ (-s t) * F (s t)) = G i t
    rw [hscale]
    dsimp [G]
    ring
  convert hi using 1
  · funext i
    exact hsingle i
  · congr 1
    apply integral_congr_ae
    filter_upwards with t
    simp only [G, s, tsum_mul_right]
    ring

end ArtinMatthews
