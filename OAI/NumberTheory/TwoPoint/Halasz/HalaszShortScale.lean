module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
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


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! Integer short-variable lengths for the logarithmic bilinear argument. -/
namespace TwoPointCorrelations

noncomputable def halaszShortScale (N α : ℝ) : ℕ := ⌊N^α⌋₊

lemma halasz_short_scale_bounds {N α : ℝ} (hN : 1≤N) (hα : 0≤α) :
    1≤halaszShortScale N α ∧ N^α≤2*(halaszShortScale N α:ℝ) ∧
      (halaszShortScale N α:ℝ)≤N^α := by
  have hy : 1≤N^α := Real.one_le_rpow hN hα
  have hy0 : 0≤N^α := by linarith
  have hp : 1≤halaszShortScale N α := (Nat.le_floor_iff hy0).mpr (by exact_mod_cast hy)
  have hpR : 1≤(halaszShortScale N α:ℝ) := by exact_mod_cast hp
  refine ⟨hp,?_,Nat.floor_le hy0⟩
  have hh : N^α<(halaszShortScale N α:ℝ)+1 := Nat.lt_floor_add_one _
  linarith

lemma halasz_short_scale_square {N α : ℝ} (hN : 1≤N) (hα : 0≤α) :
    (halaszShortScale N α:ℝ)^2≤N^(2*α) := by
  have hb := (halasz_short_scale_bounds hN hα).2.2
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) hb 2
  convert hh using 1
  rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0≤N)]
  congr 1
  ring

lemma halasz_short_scale_le_base {N α : ℝ} (hN : 1≤N) (hα : 0≤α) (hα1 : α≤1) :
    (halaszShortScale N α:ℝ)≤N := by
  apply (halasz_short_scale_bounds hN hα).2.2.trans
  convert Real.rpow_le_rpow_of_exponent_le hN hα1 using 1
  exact (Real.rpow_one N).symm

end TwoPointCorrelations

end OAI
