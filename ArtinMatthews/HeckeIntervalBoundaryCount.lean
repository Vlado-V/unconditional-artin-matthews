module

public import ArtinMatthews.HeckeIntervalCutoff
public import ArtinMatthews.HeckeIntervalBoundary
public import ArtinMatthews.MarkedMajorArcSmoothing
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! Integer counting gives an explicit O(εH+1) boundary error for every
moving logarithmic subinterval of the fixed dyadic range. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators Classical

theorem heckeInterval_exp_width {ε : ℝ} (hε : 0 ≤ ε) (hεh : ε ≤ 1/2) :
    Real.exp ε-1 ≤ 2*ε := by
  have he := Real.exp_bound_div_one_sub_of_interval hε (show ε < 1 by linarith)
  have hd : 0 < 1-ε := by linarith
  have hb : 1/(1-ε) ≤ 1+2*ε := (div_le_iff₀ hd).mpr (by nlinarith)
  linarith

theorem heckeLogInterval_strip_card {ε u H : ℝ}
    (hε : 0 < ε) (hεh : ε ≤ 1/2) (hu : u ≤ Real.log 2) (hH : 0 < H)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    ((S.filter (fun n : ℕ => u<Real.log ((n : ℝ)/H) ∧
      Real.log ((n : ℝ)/H)<u+ε)).card : ℝ) ≤ 4*ε*H+1 := by
  let x := Real.exp u*H
  let y := Real.exp (u+ε)*H
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxy : x ≤ y := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hH.le
  have hsub : S.filter (fun n : ℕ => u<Real.log ((n : ℝ)/H) ∧
      Real.log ((n : ℝ)/H)<u+ε) ⊆
      S.filter (fun n : ℕ => x<(n : ℝ) ∧ (n : ℝ)<y) := by
    intro n hn
    obtain ⟨hnS, hlo, hhi⟩ := Finset.mem_filter.mp hn
    have hnpos : 0 < (n : ℝ)/H := div_pos (by exact_mod_cast hS n hnS) hH
    have hlo' : Real.exp u < (n : ℝ)/H := by
      simpa only [Real.exp_log hnpos] using Real.exp_lt_exp.mpr hlo
    have hhi' : (n : ℝ)/H < Real.exp (u+ε) := by
      simpa only [Real.exp_log hnpos] using Real.exp_lt_exp.mpr hhi
    exact Finset.mem_filter.mpr ⟨hnS, (lt_div_iff₀ hH).mp hlo', (div_lt_iff₀ hH).mp hhi'⟩
  have hcard : ((S.filter (fun n : ℕ => u<Real.log ((n : ℝ)/H) ∧
      Real.log ((n : ℝ)/H)<u+ε)).card : ℝ) ≤ y-x+1 := by
    have hle : ((S.filter (fun n : ℕ => u<Real.log ((n : ℝ)/H) ∧
        Real.log ((n : ℝ)/H)<u+ε)).card : ℝ) ≤
        ((S.filter (fun n : ℕ => x<(n : ℝ) ∧ (n : ℝ)<y)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hle.trans (marked_smoothing_boundary_card hx hxy S)
  have he : Real.exp u ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hu
  have hw : y-x ≤ 4*ε*H := by
    calc
      _ = (Real.exp u*(Real.exp ε-1))*H := by dsimp [x, y]; rw [Real.exp_add]; ring
      _ ≤ (2*(2*ε))*H := mul_le_mul_of_nonneg_right
        (mul_le_mul he (heckeInterval_exp_width hε.le hεh)
          (by linarith [Real.add_one_le_exp ε]) (by norm_num)) hH.le
      _ = _ := by ring
  linarith

theorem heckeLogInterval_finite_boundary_bound {ε u v H M : ℝ}
    (hε : 0 < ε) (hεh : ε ≤ 1/2) (huv : u ≤ v) (hv : v ≤ Real.log 2)
    (hH : 0 < H) (hM : 0 ≤ M) (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) (ha : ∀ n ∈ S, ‖a n‖ ≤ M) :
    ‖(∑ n ∈ S, a n*heckeLogIntervalCutoff ε u v ((n : ℝ)/H)) -
      (∑ n ∈ S, a n*(if u<Real.log ((n : ℝ)/H) ∧ Real.log ((n : ℝ)/H)≤v
        then (1 : ℂ) else 0))‖ ≤ 2*M*(8*ε*H+2) := by
  apply (heckeLogInterval_finite_boundary hε huv hH hM S a hS ha).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*M)
  have hleft := heckeLogInterval_strip_card hε hεh (huv.trans hv) hH S hS
  have hright := heckeLogInterval_strip_card hε hεh hv hH S hS
  linarith

end ArtinMatthews
