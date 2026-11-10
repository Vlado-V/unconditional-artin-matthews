module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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

/-! Explicit polynomial lower-height and exponential upper-height budgets
for the actual major-arc contour, with no analytic hypotheses. -/
namespace ArtinMatthews

open Filter
open scoped Topology

lemma marked_major_frequency_budget (B T τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, ∀ t u : ℝ,
      L^(B+2) ≤ |t| → |t| ≤ Real.exp (2*L) → Real.exp (τ*L) ≤ u →
      0 < L^B ∧ L^B ≤ |t|/2 ∧ 2*T ≤ |t| ∧
      2*|t| ≤ Real.exp (3*L) ∧ 1 ≤ u ∧ 1 ≤ Real.log u := by
  have hTp : 0 < B+2 := by linarith
  have hT := (tendsto_rpow_atTop hTp).eventually (eventually_ge_atTop (2*T))
  filter_upwards [hT,eventually_ge_atTop (max 2 (1/τ))] with L hTL hL
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLτ : 1/τ ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith
  have hτL : 1 ≤ τ*L := by
    have hh := (div_le_iff₀ hτ).mp hLτ
    nlinarith
  intro t u htlo hthi hu
  have hp : 0 < L^B := Real.rpow_pos_of_pos hLp _
  have hrpow : L^(B+2) = L^B*L^2 := by rw [Real.rpow_add hLp,Real.rpow_two]
  have htw : 2*L^B ≤ |t| := by
    calc
      _ ≤ L^B*L^2 := by nlinarith [sq_nonneg (L-2)]
      _ = L^(B+2) := hrpow.symm
      _ ≤ _ := htlo
  have hupper : 2*|t| ≤ Real.exp (3*L) := by
    have hexp : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    calc
      _ ≤ 2*Real.exp (2*L) := mul_le_mul_of_nonneg_left hthi (by norm_num)
      _ ≤ Real.exp L*Real.exp (2*L) := mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hu0 : 0 < u := (Real.exp_pos _).trans_le hu
  have hlogu : 1 ≤ Real.log u := hτL.trans ((Real.le_log_iff_exp_le hu0).mpr hu)
  have hu1 : 1 ≤ u := by
    exact (Real.one_le_exp_iff.mpr (by linarith : 0 ≤ τ*L)).trans hu
  exact ⟨hp,by linarith,hTL.trans htlo,hupper,hu1,hlogu⟩

end ArtinMatthews
