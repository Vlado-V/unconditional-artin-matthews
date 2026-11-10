module

public import ArtinMatthews.SpectralKLMacdonaldAnalysis
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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine uniform L2 bound for the noncompact Macdonald profile
on physical compact supports.  The actual positive exponential controls
both physical tails; KL Plancherel transfers the bound to the K product. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralKLExpReciprocal_norm_pos (a b : ℝ) {z : ℝ} (hz : 0 < z) :
    ‖spectralKLExpReciprocal a b z‖ = Real.exp (-a*z-b/z) := by
  rw [spectralKLExpReciprocal,ite_eq_left hz,Complex.norm_exp,
    show -(a : ℂ)*(z : ℂ)-(b : ℂ)/(z : ℂ) = ((-a*z-b/z : ℝ) : ℂ) by push_cast; rfl,
    Complex.ofReal_re]

theorem spectralKLMacdonaldProfile_norm_le {a x y : ℝ} (ha : 0 < a) (hy : 0 < y)
    (hax : a ≤ x) (z : ℝ) :
    ‖spectralKLMacdonaldProfile x y z‖ ≤ ‖spectralKLExpReciprocal 1 (a*y/2) z‖ := by
  by_cases hz : 0 < z
  · have hx : 0 < x := ha.trans_le hax
    have hden : 0 < 2*x*y := by positivity
    have hA : 1 ≤ (x^2+y^2)/(2*x*y) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith [sq_nonneg (x-y)]
    have hB : a*y/2 ≤ x*y/2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hax hy.le) (by norm_num)
    rw [spectralKLMacdonaldProfile,spectralKLExpReciprocal_norm_pos _ _ hz,
      spectralKLExpReciprocal_norm_pos _ _ hz]
    apply Real.exp_le_exp.mpr
    have hAz : z ≤ (x^2+y^2)/(2*x*y)*z := by nlinarith
    have hBz := div_le_div_of_nonneg_right hB hz.le
    linarith
  · simp only [spectralKLMacdonaldProfile,spectralKLExpReciprocal,ite_eq_right hz,le_refl]

theorem spectralKLMacdonaldProfile_uniform_norm {a x y : ℝ} (ha : 0 < a) (hy : 0 < y)
    (hax : a ≤ x) :
    ‖(spectralKLMacdonaldProfile_memLp (ha.trans_le hax) hy).toLp (spectralKLMacdonaldProfile x y)‖ ≤
      ‖(spectralKLExpReciprocal_memLp (by norm_num : (0 : ℝ) < 1) (by positivity : 0 < a*y/2)).toLp
        (spectralKLExpReciprocal 1 (a*y/2))‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [MemLp.coeFn_toLp (spectralKLMacdonaldProfile_memLp (ha.trans_le hax) hy),
    MemLp.coeFn_toLp (spectralKLExpReciprocal_memLp (by norm_num : (0 : ℝ) < 1)
      (by positivity : 0 < a*y/2))] with z hz1 hz2
  rw [hz1,hz2]
  exact spectralKLMacdonaldProfile_norm_le ha hy hax z

theorem spectralKLMacdonaldProduct_toLp_norm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ‖(spectralKLMacdonaldProduct_memLp hx hy).toLp (fun r : ℝ =>
      2*schlafliBesselK ((r : ℂ)*Complex.I) x*schlafliBesselK ((r : ℂ)*Complex.I) y)‖ =
      ‖(spectralKLMacdonaldProfile_memLp hx hy).toLp (spectralKLMacdonaldProfile x y)‖ := by
  have he : (spectralKLMacdonaldProduct_memLp hx hy).toLp (fun r : ℝ =>
      2*schlafliBesselK ((r : ℂ)*Complex.I) x*schlafliBesselK ((r : ℂ)*Complex.I) y) =
      spectralKLAnalysis ((spectralKLMacdonaldProfile_memLp hx hy).toLp (spectralKLMacdonaldProfile x y)) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (spectralKLMacdonaldProfile_completed_analysis hx hy).symm
  rw [he,spectralKLAnalysis_norm]

theorem spectralKL_L2_norm_product_square_bound {μ : Measure ℝ} (F G : ℝ → ℂ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    (∫ r : ℝ, ‖F r‖*‖G r‖ ∂μ) ≤ ‖hF.toLp F‖^2+‖hG.toLp G‖^2 := by
  have hi : Integrable (fun r : ℝ => ‖F r‖*‖G r‖) μ := by
    have h := (L2.integrable_inner (𝕜 := ℂ) (hF.toLp F) (hG.toLp G)).norm
    apply h.congr
    filter_upwards [hF.coeFn_toLp,hG.coeFn_toLp] with r hrF hrG
    rw [RCLike.inner_apply,hrF,hrG,norm_mul]
    change ‖G r‖*‖star (F r)‖ = ‖F r‖*‖G r‖
    rw [norm_star,mul_comm]
  have hF2 := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hG2 := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  calc
    _ ≤ ∫ r : ℝ, ‖F r‖^2+‖G r‖^2 ∂μ := by
      apply integral_mono hi (hF2.add hG2)
      intro r
      dsimp only [Pi.add_apply]
      nlinarith [sq_nonneg (‖F r‖-‖G r‖)]
    _ = _ := by rw [integral_add hF2 hG2,← spectral_toLp_norm_sq F hF,← spectral_toLp_norm_sq G hG]

theorem spectralKLMacdonaldProduct_uniform_pair_bound {a x y : ℝ} (ha : 0 < a) (hy : 0 < y)
    (hax : a ≤ x) (F : ℝ → ℂ) (hF : MemLp F 2 spectralKLSpectralMeasure) :
    (∫ r : ℝ, ‖2*schlafliBesselK ((r : ℂ)*Complex.I) x*
      schlafliBesselK ((r : ℂ)*Complex.I) y‖*‖F r‖ ∂spectralKLSpectralMeasure) ≤
      ‖(spectralKLExpReciprocal_memLp (by norm_num : (0 : ℝ) < 1) (by positivity : 0 < a*y/2)).toLp
        (spectralKLExpReciprocal 1 (a*y/2))‖^2+‖hF.toLp F‖^2 := by
  have hb := spectralKL_L2_norm_product_square_bound _ _
    (spectralKLMacdonaldProduct_memLp (ha.trans_le hax) hy) hF
  rw [spectralKLMacdonaldProduct_toLp_norm (ha.trans_le hax) hy] at hb
  have hu := spectralKLMacdonaldProfile_uniform_norm ha hy hax
  nlinarith [norm_nonneg ((spectralKLMacdonaldProfile_memLp (ha.trans_le hax) hy).toLp
    (spectralKLMacdonaldProfile x y)),norm_nonneg ((spectralKLExpReciprocal_memLp
      (by norm_num : (0 : ℝ) < 1) (by positivity : 0 < a*y/2)).toLp (spectralKLExpReciprocal 1 (a*y/2)))]

end ArtinMatthews
