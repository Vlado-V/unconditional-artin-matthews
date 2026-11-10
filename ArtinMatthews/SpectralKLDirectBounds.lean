module

public import ArtinMatthews.SpectralKLDirectDefinitions
public import ArtinMatthews.SpectralBesselKEquation
public import ArtinMatthews.SpectralBesselOrderAnalytic
public import ArtinMatthews.SpectralKLDirectKernel
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

namespace ArtinMatthews
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology
noncomputable section

theorem spectralKLDirectSynthesis_integrand_continuous (F : ℝ → ℂ)
    (hF : Continuous F)
    {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ => schlafliBesselK ((t : ℂ) * Complex.I) x * F t *
      (spectralKLPlancherelWeight t : ℂ)) := by
  have hK : Continuous (fun t : ℝ => schlafliBesselK ((t : ℂ) * Complex.I) x) :=
    (schlafliBesselK_order_differentiable hx).continuous.comp (by fun_prop)
  exact (hK.mul hF).mul
    (Complex.continuous_ofReal.comp spectralKLPlancherelWeight_continuous)

theorem spectralKLDirectSynthesis_integrable (F : ℝ → ℂ)
    (hF : Continuous F)
    (hrapid : SpectralKLDirectRapid F)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => schlafliBesselK ((t : ℂ) * Complex.I) x * F t *
      (spectralKLPlancherelWeight t : ℂ)) := by
  obtain ⟨C, _, hC⟩ := spectralKLDirectSynthesis_kernel_bound F hrapid
    2 (by norm_num) x hx
  apply (integrable_inv_one_add_sq.const_mul (C / x ^ 2)).mono'
    (spectralKLDirectSynthesis_integrand_continuous F hF hx).aestronglyMeasurable
  exact ae_of_all _ fun t => by simpa only [div_eq_mul_inv, mul_assoc] using hC x t le_rfl

theorem spectralKLDirectSynthesis_large_bound (F : ℝ → ℂ)
    (hrapid : SpectralKLDirectRapid F)
    (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖spectralKLDirectSynthesis F x‖ ≤ C / x ^ k := by
  obtain ⟨C, hC, henv⟩ := spectralKLDirectSynthesis_kernel_bound F hrapid
    k hk 1 (by norm_num)
  let J := ∫ t in Ioi (0 : ℝ), (1 + t ^ 2)⁻¹
  refine ⟨C * J, mul_nonneg hC (integral_nonneg (fun t => by positivity)), ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [spectralKLDirectSynthesis, ite_eq_left hx0, spectralKLWeightedSynthesis]
  have hb : ‖∫ t in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ) * Complex.I) x *
      F t * (spectralKLPlancherelWeight t : ℂ)‖ ≤
      ∫ t in Ioi (0 : ℝ), (C / x ^ k) * (1 + t ^ 2)⁻¹ := by
    apply norm_integral_le_of_norm_le
      ((integrable_inv_one_add_sq.restrict).const_mul (C / x ^ k))
    exact ae_of_all _ fun t => by simpa only [div_eq_mul_inv, mul_assoc] using henv x t hx
  have heq : (∫ t in Ioi (0 : ℝ), C / x ^ k * (1 + t ^ 2)⁻¹) = C * J / x ^ k := by
    rw [integral_const_mul]
    dsimp only [J]
    ring
  exact hb.trans_eq heq

theorem spectralKLDirectSynthesis_continuousOn (F : ℝ → ℂ)
    (hF : Continuous F)
    (hrapid : SpectralKLDirectRapid F) :
    ContinuousOn (spectralKLDirectSynthesis F) (Ioi (0 : ℝ)) := by
  intro x hx
  change 0 < x at hx
  have hnh : ∀ᶠ y : ℝ in 𝓝 x, x / 2 < y := eventually_gt_nhds (by linarith)
  have heq : spectralKLDirectSynthesis F =ᶠ[𝓝 x]
      (fun y => spectralKLWeightedSynthesis (F) y) := by
    filter_upwards [hnh] with y hy
    simp only [spectralKLDirectSynthesis, ite_eq_left (show 0 < y by linarith)]
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.congr _ heq.symm
  unfold spectralKLWeightedSynthesis
  obtain ⟨C, _, henv⟩ := spectralKLDirectSynthesis_kernel_bound F hrapid
    2 (by norm_num) (x / 2) (by linarith)
  apply continuousAt_of_dominated (bound := fun t : ℝ => (C / (x / 2) ^ 2) * (1 + t ^ 2)⁻¹)
  · filter_upwards [hnh] with y hy
    exact (spectralKLDirectSynthesis_integrable F hF hrapid (by linarith : 0 < y)).restrict.aestronglyMeasurable
  · filter_upwards [hnh] with y hy
    filter_upwards with t
    exact (henv y t hy.le).trans (by
      simp only [div_eq_mul_inv]
      gcongr
      simpa only [div_eq_mul_inv] using hy.le)
  · exact (integrable_inv_one_add_sq.restrict).const_mul _
  · filter_upwards with t
    exact (((schlafliBesselK_hasDerivAt ((t : ℂ) * Complex.I) x hx).continuousAt.mul
      continuousAt_const).mul continuousAt_const)


end
end ArtinMatthews
