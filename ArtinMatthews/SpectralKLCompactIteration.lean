module

public import ArtinMatthews.SpectralKLCompactDifferential
public import ArtinMatthews.SpectralKLCompactOrder
public import ArtinMatthews.SpectralKLDifferentialGreen
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
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff
noncomputable section

def spectralKLShiftedOperator (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  g x + spectralKLPhysicalOperator g x

def spectralKLIteratedOperator (g : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => g
  | n + 1 => spectralKLShiftedOperator (spectralKLIteratedOperator g n)

theorem spectralKLShiftedOperator_smooth (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (spectralKLShiftedOperator g) := hg.add (spectralKLPhysicalOperator_smooth g hg)

theorem spectralKLShiftedOperator_compact (g : ℝ → ℂ) (hc : HasCompactSupport g) :
    HasCompactSupport (spectralKLShiftedOperator g) := hc.add (spectralKLPhysicalOperator_compact g hc)

theorem spectralKLShiftedOperator_tsupport (g : ℝ → ℂ) :
    tsupport (spectralKLShiftedOperator g) ⊆ tsupport g := by
  apply closure_minimal _ (isClosed_tsupport g)
  intro x hx
  by_contra hn
  have hg0 := image_eq_zero_of_notMem_tsupport hn
  have hop0 := image_eq_zero_of_notMem_tsupport
    (fun hh => hn (spectralKLPhysicalOperator_tsupport g hh))
  exact hx (by simp [spectralKLShiftedOperator, hg0, hop0])

theorem spectralKLIteratedOperator_properties (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) (n : ℕ) :
    ContDiff ℝ ∞ (spectralKLIteratedOperator g n) ∧
      HasCompactSupport (spectralKLIteratedOperator g n) ∧
      tsupport (spectralKLIteratedOperator g n) ⊆ Ioi (0 : ℝ) := by
  induction n with
  | zero => exact ⟨hg, hc, hp⟩
  | succ n ih =>
      exact ⟨spectralKLShiftedOperator_smooth _ ih.1,
        spectralKLShiftedOperator_compact _ ih.2.1,
        (spectralKLShiftedOperator_tsupport _).trans ih.2.2⟩

theorem spectralKLCompactOrderTransform_shifted (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) (ν : ℂ) :
    spectralKLCompactOrderTransform (spectralKLShiftedOperator g) ν =
      (1 - ν ^ 2) * spectralKLCompactOrderTransform g ν := by
  have hgI := spectralKLCompactOrderIntegrand_integrable g hg.continuous hc hp ν
  have hLI := spectralKLCompactOrderIntegrand_integrable (spectralKLPhysicalOperator g)
    (spectralKLPhysicalOperator_smooth g hg).continuous
    (spectralKLPhysicalOperator_compact g hc) ((spectralKLPhysicalOperator_tsupport g).trans hp) ν
  have heq : spectralKLCompactOrderTransform (spectralKLShiftedOperator g) ν =
      spectralKLCompactOrderTransform g ν + spectralKLCompactOrderTransform (spectralKLPhysicalOperator g) ν := by
    unfold spectralKLCompactOrderTransform
    rw [← integral_add hgI hLI]
    apply integral_congr_ae
    filter_upwards with x
    unfold spectralKLCompactOrderIntegrand spectralKLPhysicalCompactDiv spectralKLShiftedOperator
    ring
  rw [heq, spectralKLCompactOrderTransform_operator g hg hc hp ν]
  ring

theorem spectralKLCompactOrderTransform_iterated (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) (n : ℕ) (ν : ℂ) :
    spectralKLCompactOrderTransform (spectralKLIteratedOperator g n) ν =
      (1 - ν ^ 2) ^ n * spectralKLCompactOrderTransform g ν := by
  induction n with
  | zero => simp [spectralKLIteratedOperator]
  | succ n ih =>
      obtain ⟨hn, hcn, hpn⟩ := spectralKLIteratedOperator_properties g hg hc hp n
      rw [spectralKLIteratedOperator, spectralKLCompactOrderTransform_shifted _ hn hcn hpn ν, ih,
        pow_succ]
      ring

theorem spectralKLCompactOrderTransform_strip_power (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) (n : ℕ)
    (t y : ℝ) (hy : |y| ≤ 3 / 4) :
    ((1 + t ^ 2) / 4) ^ n * ‖spectralKLCompactOrderTransform g (-(y : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ‖spectralKLCompactOrderTransform (spectralKLIteratedOperator g n)
        (-(y : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hy2 : y ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by
    rcases abs_le.mp hy with ⟨hl, hr⟩
    nlinarith
  have hreal : (1 + t ^ 2) / 4 ≤
      (1 - (-(y : ℂ) + (t : ℂ) * Complex.I) ^ 2).re := by
    norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    nlinarith [sq_nonneg t]
  have hlow : (1 + t ^ 2) / 4 ≤ ‖1 - (-(y : ℂ) + (t : ℂ) * Complex.I) ^ 2‖ :=
    hreal.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  rw [spectralKLCompactOrderTransform_iterated g hg hc hp n, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hlow n) (norm_nonneg _)

end
end ArtinMatthews
