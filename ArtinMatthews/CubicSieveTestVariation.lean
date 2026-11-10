module

public import ArtinMatthews.CubicSieveDivisorSourceWeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform variation of the original shifted smooth test. -/

noncomputable section
namespace ArtinMatthews

open MeasureTheory
open scoped ContDiff

theorem cubicSieve_shiftedTest_variation_bound (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      (∫ t in Set.Ioc x (3 * x), |deriv (cubicSieveShiftedDivisorTest Φ x) t|) ≤ C := by
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 3)).bddAbove_image
    (hΦ.continuous_deriv (by simp)).abs.continuousOn
  let D := max 1 A
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨2 * D, by positivity, fun x hx => ?_⟩
  have hx₀ := zero_lt_one.trans_le hx
  have hnorm : ∀ t ∈ Set.Ioc x (3 * x),
      ‖|deriv (cubicSieveShiftedDivisorTest Φ x) t|‖ ≤ D / x := by
    intro t ht
    have harg : (t - 1) / x ∈ Set.Icc (0 : ℝ) 3 := by
      constructor
      · exact div_nonneg (by linarith only [ht.1, hx]) hx₀.le
      · apply (div_le_iff₀ hx₀).mpr
        linarith only [ht.2]
    have hderiv : |deriv Φ ((t - 1) / x)| ≤ D :=
      (hA (Set.mem_image_of_mem _ harg)).trans (le_max_right _ _)
    rw [(cubicSieve_shiftedDivisorTest_hasDerivAt Φ (hΦ.differentiable (by simp)) x t).deriv,
      Real.norm_eq_abs, abs_abs, abs_div, abs_of_pos hx₀]
    exact div_le_div_of_nonneg_right hderiv hx₀.le
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc x (3 * x))
    (f := fun t => |deriv (cubicSieveShiftedDivisorTest Φ x) t|) (by simp only [Real.volume_Ioc, ENNReal.ofReal_lt_top]) hnorm
  rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc (fun _ _ => abs_nonneg _))] at h
  have hvolume : volume.real (Set.Ioc x (3 * x)) = 2 * x := by
    simp only [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : 0 ≤ 3 * x - x)]
    ring
  rw [hvolume] at h
  exact h.trans_eq (by field_simp)

end ArtinMatthews
