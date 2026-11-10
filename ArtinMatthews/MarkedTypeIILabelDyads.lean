module

public import ArtinMatthews.MarkedTypeIILabelCutoff
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
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

/-! The occupied smooth label dyads are a finite exact partition. Their
actual count follows from the largest label, including the empty set. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators Classical
noncomputable section

def markedTypeIILabelDyadCap (S : Finset ℕ) : ℕ := max 1 (S.sup id)

def markedTypeIILabelDyadIndices (S : Finset ℕ) : Finset ℕ :=
  (range (Nat.log 2 (markedTypeIILabelDyadCap S)+1)).filter
    (fun j => ∃ b∈S,markedTypeIILabelCutoff ((b:ℝ)/(2:ℝ)^j)≠0)

theorem markedTypeIILabelDyad_partition (S : Finset ℕ) (b : ℕ) (hb : b∈S) (hb₂ : 2≤b) :
    (∑ j∈markedTypeIILabelDyadIndices S,markedTypeIILabelCutoff ((b:ℝ)/(2:ℝ)^j))=1 := by
  let N := Nat.log 2 (markedTypeIILabelDyadCap S)+1
  have hbcap : b≤markedTypeIILabelDyadCap S := (Finset.le_sup (f:=id) hb).trans (le_max_right _ _)
  have hcap : markedTypeIILabelDyadCap S<(2:ℕ)^N :=
    Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) _
  have hN : (b:ℝ) ≤ (2:ℝ)^N := by exact_mod_cast hbcap.trans hcap.le
  calc
    _ = ∑ j∈range N,markedTypeIILabelCutoff ((b:ℝ)/(2:ℝ)^j) := by
      unfold markedTypeIILabelDyadIndices
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hnot
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hj,b,hb,hn⟩)
    _ = _ := markedTypeIILabelCutoff_partition_range N (by exact_mod_cast hb₂) hN

theorem markedTypeIILabelDyad_card (S : Finset ℕ) (Z : ℝ) (hZ : 1≤Z)
    (hcap : ∀ b∈S,(b:ℝ)≤Z) :
    ((markedTypeIILabelDyadIndices S).card:ℝ)≤1+Real.log Z/Real.log 2 := by
  let C := markedTypeIILabelDyadCap S
  have hC₁ : 1≤C := le_max_left _ _
  have hCp : (0:ℝ)<C := by exact_mod_cast (zero_lt_one.trans_le hC₁)
  have hZ₀ : 0≤Z := zero_le_one.trans hZ
  have hCn : C≤⌊Z⌋₊ := by
    apply max_le ((Nat.le_floor_iff hZ₀).mpr (by simpa only [Nat.cast_one] using hZ))
    exact Finset.sup_le (fun b hb => (Nat.le_floor_iff hZ₀).mpr (hcap b hb))
  have hC : (C:ℝ)≤Z := (by exact_mod_cast hCn : (C:ℝ)≤⌊Z⌋₊).trans (Nat.floor_le hZ₀)
  have hc : ((markedTypeIILabelDyadIndices S).card:ℝ)≤(Nat.log 2 C:ℝ)+1 := by
    have hsub : markedTypeIILabelDyadIndices S ⊆ range (Nat.log 2 C+1) := Finset.filter_subset _ _
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
  have hlog : (Nat.log 2 C:ℝ)≤Real.log Z/Real.log 2 := by
    calc
      _ ≤ Real.logb 2 (C:ℝ) := Real.natLog_le_logb _ _
      _ ≤ _ := div_le_div_of_nonneg_right (Real.log_le_log hCp hC) (Real.log_nonneg (by norm_num))
  linarith

end
end ArtinMatthews
