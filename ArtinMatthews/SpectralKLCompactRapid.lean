module

public import ArtinMatthews.SpectralKLCompactOrder
public import ArtinMatthews.SpectralKLCompactIteration
public import ArtinMatthews.SpectralKShiftedPointBound
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory OAI.CubicEisenstein
open scoped ContDiff
noncomputable section

theorem spectralKLCompactOrderTransform_strip_bound (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ t : ℝ, |δ| ≤ 3 / 4 →
      Real.exp (Real.pi * |t| / 2) *
        ‖spectralKLCompactOrderTransform g ((δ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      C * (1 + |t|) ^ 2 := by
  obtain ⟨a, ha, hsupport⟩ := spectral_compact_positive_lower_bound g hc hp
  obtain ⟨C, hC, hK⟩ := schlafliBesselK_closed_strip_polynomial_bound 2 (3 / 4) a
    (by norm_num) (by norm_num) ha
  let mass := ∫ x : ℝ, ‖spectralKLPhysicalCompactDiv g x‖
  refine ⟨C / a ^ 2 * mass, by dsimp [mass]; positivity, ?_⟩
  intro δ t hδ
  let E := Real.exp (Real.pi * |t| / 2)
  let b := C * (1 + |t|) ^ 2 / a ^ 2
  have hdiv := spectralKLPhysicalCompactDiv_integrable g hg hc hp
  have hi := spectralKLCompactOrderIntegrand_integrable g hg hc hp
    ((δ : ℂ) + (t : ℂ) * Complex.I)
  have hbound (x : ℝ) : E * ‖spectralKLCompactOrderIntegrand g
      ((δ : ℂ) + (t : ℂ) * Complex.I) x‖ ≤ b * ‖spectralKLPhysicalCompactDiv g x‖ := by
    by_cases hx : g x = 0
    · simp [spectralKLCompactOrderIntegrand, spectralKLPhysicalCompactDiv, hx]
    · have hax := hsupport x (subset_tsupport g hx)
      have hxx : 0 < x := ha.trans_le hax
      have hkernel : E * ‖schlafliBesselK ((δ : ℂ) + (t : ℂ) * Complex.I) x‖ ≤ b :=
        (hK δ t x hδ hax).trans (div_le_div_of_nonneg_left (by positivity)
          (sq_pos_of_pos ha) (pow_le_pow_left₀ ha.le hax 2))
      dsimp only [spectralKLCompactOrderIntegrand]
      rw [norm_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hkernel (norm_nonneg _)
  calc
    _ ≤ E * ∫ x : ℝ, ‖spectralKLCompactOrderIntegrand g
        ((δ : ℂ) + (t : ℂ) * Complex.I) x‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Real.exp_nonneg _)
    _ = ∫ x : ℝ, E * ‖spectralKLCompactOrderIntegrand g
        ((δ : ℂ) + (t : ℂ) * Complex.I) x‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ x : ℝ, b * ‖spectralKLPhysicalCompactDiv g x‖ :=
      integral_mono_ae (hi.norm.const_mul E) (hdiv.norm.const_mul b) (ae_of_all _ hbound)
    _ = _ := by rw [integral_const_mul]; dsimp [b, mass]; ring

theorem spectralKLCompactOrderTransform_strip_rapid (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y t : ℝ, |y| ≤ 3 / 4 →
      (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t| / 2) *
        ‖spectralKLCompactOrderTransform g (-(y : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨hn, hcn, hpn⟩ := spectralKLIteratedOperator_properties g hg hc hp (N + 1)
  obtain ⟨C, hC, hbound⟩ := spectralKLCompactOrderTransform_strip_bound
    (spectralKLIteratedOperator g (N + 1)) hn.continuous hcn hpn
  refine ⟨2 * C * 4 ^ (N + 1), by positivity, ?_⟩
  intro y t hy
  let u := 1 + t ^ 2
  let E := Real.exp (Real.pi * |t| / 2)
  let f := ‖spectralKLCompactOrderTransform g (-(y : ℂ) + (t : ℂ) * Complex.I)‖
  have hu : 0 < u := by dsimp [u]; positivity
  have hh := mul_le_mul_of_nonneg_left
    (spectralKLCompactOrderTransform_strip_power g hg hc hp (N + 1) t y hy)
    (Real.exp_nonneg (Real.pi * |t| / 2))
  have hb := hbound (-y) t (by simpa only [abs_neg] using hy)
  rw [Complex.ofReal_neg] at hb
  have hsmall : E * ((u / 4) ^ (N + 1) * f) ≤ 2 * C * u := by
    apply hh.trans
    apply hb.trans
    have ht : (1 + |t|) ^ 2 ≤ 2 * u := by dsimp [u]; nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
    exact (mul_le_mul_of_nonneg_left ht hC).trans_eq (by ring)
  have hscale : E * ((u / 4) ^ (N + 1) * f) =
      (u / 4 ^ (N + 1)) * (u ^ N * E * f) := by rw [div_pow, pow_succ]; ring
  rw [hscale] at hsmall
  have hfour : (0 : ℝ) < 4 ^ (N + 1) := by positivity
  have hscaled : (u / 4 ^ (N + 1)) * (u ^ N * E * f) ≤
      (u / 4 ^ (N + 1)) * (2 * C * 4 ^ (N + 1)) := by
    have heq : (u / 4 ^ (N + 1)) * (2 * C * 4 ^ (N + 1)) = 2 * C * u := by
      field_simp
    rw [heq]
    exact hsmall
  have hout := le_of_mul_le_mul_left hscaled (div_pos hu hfour)
  exact hout

end
end ArtinMatthews
