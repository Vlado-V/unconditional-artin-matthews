module

public import ArtinMatthews.SpectralKLDirectDefinitions
public import ArtinMatthews.SpectralKLDirectBounds
public import ArtinMatthews.SpectralKLDirectIAnalytic
public import ArtinMatthews.SpectralKLDirectIIdentity
public import ArtinMatthews.SpectralKLInverseIIdentity
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
open scoped ContDiff
noncomputable section

theorem spectralKLDirectSynthesis_I_integral (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hF : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F)
    {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ, spectralKLDirectIIntegrand F x (t : ℂ)) =
      ((Real.pi : ℂ) * Complex.I) * spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ)) x := by
  have hi := spectralKLDirectIIntegrand_integrable_line F hF hrapid hx
    (y := 0) le_rfl (by norm_num)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hi
  rw [spectral_integral_positive_pair _ hi]
  rw [spectralKLDirectSynthesis, ite_eq_left hx, spectralKLWeightedSynthesis, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simpa only [Complex.ofReal_neg] using spectralKLDirectIIntegrand_pair F heven hx t

theorem spectralKLDirectSynthesis_small_bound (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hF : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ)) x‖ ≤ C * x ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, henv⟩ := spectralKLDirectIIntegrand_strip_bound F hrapid
  let J := ∫ t : ℝ, (1 + t ^ 2)⁻¹
  have hJ : 0 ≤ J := integral_nonneg (fun t => by positivity)
  refine ⟨C * Real.exp 1 * J / Real.pi, by positivity, ?_⟩
  intro x hx hx1
  have heq := (spectralKLDirectSynthesis_I_integral F heven hF hrapid hx).symm.trans
    (spectralKLDirectIIntegrand_shift F hF hrapid hx)
  have hboundt (t : ℝ) :
      ‖spectralKLDirectIIntegrand F x ((t : ℂ) + (3 / 4 : ℂ) * Complex.I)‖ ≤
        (C * Real.exp 1 * x ^ (3 / 4 : ℝ)) * (1 + t ^ 2)⁻¹ := by
    have hh := henv t (3 / 4) x (by norm_num) le_rfl hx
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hh
    apply hh.trans
    rw [div_eq_mul_inv]
    gcongr
  have hi := norm_integral_le_of_norm_le
    (integrable_inv_one_add_sq.const_mul (C * Real.exp 1 * x ^ (3 / 4 : ℝ))) (ae_of_all _ hboundt)
  rw [← heq, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_I, mul_one, integral_const_mul] at hi
  calc
    _ ≤ ((C * Real.exp 1 * x ^ (3 / 4 : ℝ)) * J) / Real.pi := by
      apply (le_div_iff₀ Real.pi_pos).mpr
      calc
        _ = Real.pi * ‖spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ)) x‖ := by ring
        _ ≤ _ := hi
    _ = _ := by ring

theorem spectralKLDirectSynthesis_global_power_bound (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hF : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ)) x‖ ≤ C * x ^ (3 / 4 : ℝ) := by
  obtain ⟨S, hS, hs⟩ := spectralKLDirectSynthesis_small_bound F heven hF hrapid
  obtain ⟨L, hL, hl⟩ := spectralKLDirectSynthesis_large_bound
    (fun t : ℝ => F (t : ℂ)) (spectralKLDirectStripRapid_real hrapid) 2 (by norm_num)
  refine ⟨S + L, add_nonneg hS hL, ?_⟩
  intro x hx
  by_cases hx1 : x ≤ 1
  · exact (hs x hx hx1).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · have h1 : 1 ≤ x := le_of_not_ge hx1
    have hp1 : 1 ≤ x ^ (3 / 4 : ℝ) := Real.one_le_rpow h1 (by norm_num)
    calc
      _ ≤ L / x ^ 2 := hl x h1
      _ ≤ L := div_le_self hL (one_le_pow₀ h1)
      _ ≤ (S + L) * x ^ (3 / 4 : ℝ) := by nlinarith

end
end ArtinMatthews
