module

public import ArtinMatthews.SpectralKLDirectDefinitions
public import ArtinMatthews.SpectralKXDerivatives
public import ArtinMatthews.SpectralDerivativeTowerSmooth
public import ArtinMatthews.SpectralKLInverseKEnvelope
public import ArtinMatthews.SpectralKLWindowDerivatives
public import ArtinMatthews.SpectralKXDerivativeBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
open scoped Topology ContDiff
noncomputable section

def spectralKLDirectSynthesisDerivative (n : ℕ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then ∫ t in Ioi (0 : ℝ), spectralKXDerivative n ((t : ℂ) * Complex.I) x *
    F t * (spectralKLPlancherelWeight t : ℂ) else 0

@[simp] theorem spectralKLDirectSynthesisDerivative_zero (F : ℝ → ℂ) :
    spectralKLDirectSynthesisDerivative 0 F = spectralKLDirectSynthesis F := rfl

theorem spectralKLDirectDerivative_integrand_bound (n : ℕ) (F : ℝ → ℂ)
    (hrapid : SpectralKLDirectRapid F)
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x t : ℝ, a ≤ x →
      ‖spectralKXDerivative n ((t : ℂ) * Complex.I) x * F t *
        (spectralKLPlancherelWeight t : ℂ)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨K, hK, hDK⟩ := spectralKXDerivative_compact_bound n a ha
  obtain ⟨Cdata, hCdata, hData⟩ := hrapid (n + 4)
  refine ⟨(2 / Real.pi ^ 2) * K * Cdata * 2 ^ (n + 2), by positivity, ?_⟩
  intro x t hax
  have he : (Real.exp (Real.pi * |t| / 2)) ^ 2 = Real.exp (Real.pi * |t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hd : (1 + t ^ 2) ^ ((n + 2) + 2) * Real.exp (Real.pi * |t| / 2) *
      ‖F t‖ ≤ Cdata := by simpa only [Nat.add_assoc] using hData t
  have hk : Real.exp (Real.pi * |t| / 2) * ‖spectralKXDerivative n ((t : ℂ) * Complex.I) x‖ ≤
      K * (1 + |t|) ^ (n + 2) / (1 : ℝ) ^ (n + 2) := by simpa only [one_pow, div_one] using hDK t x hax
  have hb := spectralKLInverseKEnvelope_scalar (n + 2) t 1 (Real.exp (Real.pi * |t| / 2)) K Cdata
    ‖spectralKXDerivative n ((t : ℂ) * Complex.I) x‖ ‖F t‖ |spectralKLPlancherelWeight t|
    zero_lt_one (Real.exp_pos _) hK.le hCdata (norm_nonneg _) (norm_nonneg _) (abs_nonneg _)
    hk hd (by rw [he]; exact spectralKLPlancherelWeight_abs_bound t)
  simpa only [one_pow, div_one, norm_mul, Complex.norm_real, Real.norm_eq_abs] using hb

theorem spectralKLDirectDerivative_integrand_continuous (n : ℕ) (F : ℝ → ℂ)
    (hF : Continuous F)
    {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ => spectralKXDerivative n ((t : ℂ) * Complex.I) x *
      F t * (spectralKLPlancherelWeight t : ℂ)) :=
  (((spectralKXDerivative_order_continuous n hx).comp (by fun_prop)).mul
    hF).mul
      (Complex.continuous_ofReal.comp spectralKLPlancherelWeight_continuous)

theorem spectralKLDirectSynthesisDerivative_hasDerivAt (n : ℕ) (F : ℝ → ℂ)
    (hF : Continuous F)
    (hrapid : SpectralKLDirectRapid F)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (spectralKLDirectSynthesisDerivative n F)
      (spectralKLDirectSynthesisDerivative (n + 1) F x) x := by
  let K (m : ℕ) (y t : ℝ) := spectralKXDerivative m ((t : ℂ) * Complex.I) y *
    F t * (spectralKLPlancherelWeight t : ℂ)
  obtain ⟨C, _, hC⟩ := spectralKLDirectDerivative_integrand_bound (n + 1) F hrapid (x / 2) (by linarith)
  obtain ⟨D, _, hD⟩ := spectralKLDirectDerivative_integrand_bound n F hrapid x hx
  have hi : Integrable (K n x) (volume.restrict (Ioi (0 : ℝ))) := by
    apply (integrable_inv_one_add_sq.restrict.const_mul D).mono'
      ((spectralKLDirectDerivative_integrand_continuous n F hF hx).aestronglyMeasurable)
    exact ae_of_all _ fun t => by simpa only [K, div_eq_mul_inv] using hD x t le_rfl
  have hr := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := K n) (F' := K (n + 1)) (μ := volume.restrict (Ioi (0 : ℝ)))
    (s := Ioi (x / 2)) (Ioi_mem_nhds (by linarith : x / 2 < x))
    (by
      filter_upwards [eventually_gt_nhds (by linarith : (0 : ℝ) < x)] with y hy
      exact (spectralKLDirectDerivative_integrand_continuous n F hF hy).aestronglyMeasurable)
    hi
    ((spectralKLDirectDerivative_integrand_continuous (n + 1) F hF hx).aestronglyMeasurable)
    (ae_of_all _ fun t y hy => by simpa only [K, div_eq_mul_inv] using hC y t hy.le)
    (integrable_inv_one_add_sq.restrict.const_mul C)
    (ae_of_all _ fun t y hy =>
      ((spectralKXDerivative_hasDerivAt n ((t : ℂ) * Complex.I) y (by have hy' : x / 2 < y := hy; linarith : 0 < y)).mul_const
        (F t)).mul_const (spectralKLPlancherelWeight t : ℂ))).2
  have heq : spectralKLDirectSynthesisDerivative n F =ᶠ[𝓝 x]
      (fun y => ∫ t in Ioi (0 : ℝ), K n y t) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp only [spectralKLDirectSynthesisDerivative, ite_eq_left hy, K]
  rw [spectralKLDirectSynthesisDerivative, ite_eq_left hx]
  exact hr.congr_of_eventuallyEq heq

theorem spectralKLDirectSynthesis_contDiffOn (F : ℝ → ℂ)
    (hF : Continuous F)
    (hrapid : SpectralKLDirectRapid F) :
    ContDiffOn ℝ ∞ (spectralKLDirectSynthesis F) (Ioi (0 : ℝ)) := by
  have hhigher := spectral_contDiffOn_of_hasDerivAt_tower
    (fun n => spectralKLDirectSynthesisDerivative n F) isOpen_Ioi
    (fun n x hx => spectralKLDirectSynthesisDerivative_hasDerivAt n F hF hrapid hx)
  simpa only [spectralKLDirectSynthesisDerivative_zero] using hhigher 0

end
end ArtinMatthews
