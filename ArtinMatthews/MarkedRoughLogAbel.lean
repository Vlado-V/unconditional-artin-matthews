module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import ArtinMatthews.MarkedRoughCenteredAbel
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Covering.Besicovitch
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

/-! Removing the logarithmic weight preserves its continuous counting term. -/
namespace ArtinMatthews
open Finset MeasureTheory
noncomputable section

theorem marked_log_weight_centered_interval_bound (a : ℕ → ℂ) (m : ℂ)
    {u v D : ℝ} (hu : 0 < u) (hlog : 1 ≤ Real.log u) (huv : u ≤ v)
    (hvu : v ≤ 2 * u) (hD : 0 ≤ D)
    (hprefix : ∀ w ∈ Set.Icc u v,
      ‖(∑ n ∈ Icc 0 ⌊w⌋₊, a n) - m * (w : ℂ)‖ ≤ D) :
    ‖(∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, ((Real.log n)⁻¹ : ℝ) * a n) -
      m * ((∫ t in u..v, (Real.log t)⁻¹ : ℝ) : ℂ)‖ ≤ 3 * D := by
  let φ : ℝ → ℂ := fun x => ((Real.log x)⁻¹ : ℝ)
  let φ' : ℝ → ℂ := fun x => (-x⁻¹ / (Real.log x)^2 : ℝ)
  have hxpos (x : ℝ) (hx : x ∈ Set.Icc u v) : 0 < x := hu.trans_le hx.1
  have hxlog (x : ℝ) (hx : x ∈ Set.Icc u v) : 1 ≤ Real.log x :=
    hlog.trans (Real.log_le_log hu hx.1)
  have hd (x : ℝ) (hx : x ∈ Set.Icc u v) : HasDerivAt φ (φ' x) x :=
    ((Real.hasDerivAt_log (hxpos x hx).ne').inv (by linarith [hxlog x hx])).ofReal_comp
  have hc : ContinuousOn φ' (Set.Icc u v) := by
    intro x hx
    have hlogne : Real.log x ≠ 0 := by linarith [hxlog x hx]
    exact (Complex.continuous_ofReal.continuousAt.comp
      (((continuousAt_id.inv₀ (hxpos x hx).ne').neg).div
        ((Real.continuousAt_log (hxpos x hx).ne').pow 2)
          (pow_ne_zero 2 hlogne))).continuousWithinAt
  have hval (x : ℝ) (hx : x ∈ Set.Icc u v) : ‖φ x‖ ≤ 1 := by
    have hlogp : 0 < Real.log x := by linarith [hxlog x hx]
    simp only [φ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlogp)]
    exact inv_le_one_of_one_le₀ (hxlog x hx)
  have hder (x : ℝ) (hx : x ∈ Set.Icc u v) : ‖φ' x‖ ≤ 1 / u := by
    have hlogp : 0 < Real.log x := by linarith [hxlog x hx]
    have hsq : 1 ≤ (Real.log x)^2 := by nlinarith [hxlog x hx]
    simp only [φ', Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (inv_pos.mpr (hxpos x hx)), abs_of_nonneg (sq_nonneg (Real.log x))]
    exact (div_le_self (inv_nonneg.mpr (hxpos x hx).le) hsq).trans
      (by simpa only [one_div] using one_div_le_one_div_of_le hu hx.1)
  have hb := marked_centered_abel_bound a m φ φ' hu.le huv
    (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 1 / u) hd hc hval hder hprefix
  have hmain : (∫ t in u..v, φ t) = ((∫ t in u..v, (Real.log t)⁻¹ : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  rw [hmain] at hb
  apply hb.trans
  have hfac : (1 / u) * (v - u) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (show v - u ≤ u by linarith)
      (by positivity : 0 ≤ 1 / u)).trans_eq (by field_simp)
  nlinarith

end
end ArtinMatthews
