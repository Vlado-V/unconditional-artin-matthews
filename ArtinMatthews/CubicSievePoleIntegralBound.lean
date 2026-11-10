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

/-! A uniform bound for the literal shifted double-pole contribution. -/

noncomputable section
namespace ArtinMatthews

open MeasureTheory

theorem cubicSieve_poleIntegral_abs_le (Φ : ℝ → ℝ) (hΦ : ∀ t, |Φ t| ≤ 1)
    {x : ℝ} (hx : 1 < x)
    (hL : Real.log 3 + 2 * |Real.eulerMascheroniConstant| ≤ Real.log x) (J J' : ℝ) :
    |∫ t in Set.Ioc x (3 * x), cubicSieveShiftedDivisorTest Φ x t *
      ((Real.log t + 2 * Real.eulerMascheroniConstant) * J + J')| ≤
      2 * x * (2 * Real.log x * |J| + |J'|) := by
  have hx₀ := zero_lt_one.trans hx
  have hbound (t : ℝ) (ht : t ∈ Set.Ioc x (3 * x)) :
      ‖cubicSieveShiftedDivisorTest Φ x t * ((Real.log t + 2 * Real.eulerMascheroniConstant) * J + J')‖ ≤
        2 * Real.log x * |J| + |J'| := by
    have ht₀ := hx₀.trans ht.1
    have hlog₀ := Real.log_nonneg (le_trans hx.le ht.1.le)
    have hlog : Real.log t ≤ Real.log 3 + Real.log x := by
      have h := Real.log_le_log ht₀ ht.2
      rwa [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx₀.ne'] at h
    have hlogabs : |Real.log t + 2 * Real.eulerMascheroniConstant| ≤ 2 * Real.log x := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg hlog₀, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |(Real.log t + 2 * Real.eulerMascheroniConstant) * J + J'| :=
        mul_le_of_le_one_left (abs_nonneg _) (hΦ _)
      _ ≤ |Real.log t + 2 * Real.eulerMascheroniConstant| * |J| + |J'| := by
        simpa only [abs_mul] using abs_add_le ((Real.log t + 2 * Real.eulerMascheroniConstant) * J) J'
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hlogabs (abs_nonneg _)) le_rfl
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc x (3 * x))
    (by simp only [Real.volume_Ioc, ENNReal.ofReal_lt_top]) hbound
  have hvolume : volume.real (Set.Ioc x (3 * x)) = 2 * x := by
    simp only [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : 0 ≤ 3 * x - x)]
    ring
  rw [Real.norm_eq_abs, hvolume] at h
  exact h.trans_eq (mul_comm _ _)

end ArtinMatthews
