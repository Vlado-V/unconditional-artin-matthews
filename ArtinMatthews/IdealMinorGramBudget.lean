module

public import ArtinMatthews.MarkedMinorArcGram
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

/-! The genuine Gram budget in probability normalization, including its
large-denominator and maximum-denominator gains. -/
namespace ArtinMatthews

theorem idealMinorGramBudget_normalized (U V r : ℕ) (hU : 0 < U) (hV : 0 < V)
    (hr : 0 < r) :
    markedMinorGramBudget U V r / ((U : ℝ)*(V : ℝ)) ≤
      24*(1/(V : ℝ) + 1/(r : ℝ) + (1+Real.log (2*(r : ℝ)))/(U : ℝ) +
        (r : ℝ)*(1+Real.log (2*(r : ℝ)))/((U : ℝ)*(V : ℝ))) := by
  have hUp : (0 : ℝ) < U := by exact_mod_cast hU
  have hVp : (0 : ℝ) < V := by exact_mod_cast hV
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  let H := 1+Real.log (2*(r : ℝ))
  have hH : 0 ≤ H := by
    dsimp [H]
    have hl := Real.log_nonneg (show 1 ≤ 2*(r : ℝ) by linarith)
    linarith
  have hfirst : 2*((2*V+1 : ℕ) : ℝ)/(r : ℝ)+1 ≤ 6*(V : ℝ)/(r : ℝ)+1 := by
    apply add_le_add_left
    apply div_le_div_of_nonneg_right _ hrp.le
    push_cast
    linarith
  have hb : markedMinorGramBudget U V r ≤
      24*((U : ℝ)+(U : ℝ)*(V : ℝ)/(r : ℝ)+(V : ℝ)*H+(r : ℝ)*H) := by
    unfold markedMinorGramBudget
    change (2*((2*V+1 : ℕ) : ℝ)/(r : ℝ)+1) * (2*(U : ℝ)+4*(r : ℝ)*H) ≤ _
    calc
      _ ≤ (6*(V : ℝ)/(r : ℝ)+1) * (2*(U : ℝ)+4*(r : ℝ)*H) :=
        mul_le_mul_of_nonneg_right hfirst (by positivity)
      _ = 12*(U : ℝ)*(V : ℝ)/(r : ℝ)+2*(U : ℝ)+24*(V : ℝ)*H+4*(r : ℝ)*H := by
        field_simp
        ring
      _ ≤ _ := by
        have huv : 0 ≤ (U : ℝ)*(V : ℝ)/(r : ℝ) := by positivity
        have hqh : 0 ≤ (r : ℝ)*H := mul_nonneg hrp.le hH
        simp only [div_eq_mul_inv] at huv ⊢
        nlinarith
  have hc := div_le_div_of_nonneg_right hb (mul_pos hUp hVp).le
  refine hc.trans_eq ?_
  dsimp [H]
  field_simp

theorem idealMinorGramBudget_branch (U V r : ℕ) (hU : 0 < U) (hV : 0 < V)
    (hr : 0 < r) {Q S H : ℝ} (hQ : 0 < Q) (hS : 0 < S)
    (hQr : Q ≤ (r : ℝ)) (hrS : (r : ℝ) ≤ (U : ℝ)*(V : ℝ)/S)
    (hH : 1+Real.log (2*(r : ℝ)) ≤ H) :
    markedMinorGramBudget U V r / ((U : ℝ)*(V : ℝ)) ≤
      24*(1/(V : ℝ) + 1/Q + H/(U : ℝ) + H/S) := by
  have hUp : (0 : ℝ) < U := by exact_mod_cast hU
  have hVp : (0 : ℝ) < V := by exact_mod_cast hV
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog : 0 ≤ 1+Real.log (2*(r : ℝ)) := by
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hl := Real.log_nonneg (show 1 ≤ 2*(r : ℝ) by linarith)
    linarith
  have hHp : 0 ≤ H := hlog.trans hH
  apply (idealMinorGramBudget_normalized U V r hU hV hr).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have h₁ := one_div_le_one_div_of_le hQ hQr
  have h₂ := div_le_div_of_nonneg_right hH hUp.le
  have h₃ : (r : ℝ)*(1+Real.log (2*(r : ℝ)))/((U : ℝ)*(V : ℝ)) ≤ H/S := by
    apply (div_le_iff₀ (mul_pos hUp hVp)).mpr
    have hx := mul_le_mul hrS hH hlog (by positivity : 0 ≤ (U : ℝ)*(V : ℝ)/S)
    calc
      _ ≤ ((U : ℝ)*(V : ℝ)/S)*H := hx
      _ = _ := by ring
  linarith

end ArtinMatthews
