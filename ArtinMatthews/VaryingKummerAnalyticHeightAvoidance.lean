module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
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

/-! A finite set of bad ordinates leaves a quantitative gap in every
unit height interval. This is independent of zero separation near one. -/

namespace ArtinMatthews.VaryingKummerAnalytic

theorem exists_height_avoiding_finset (S : Finset ℝ) (T : ℝ) :
    ∃ t ∈ Set.Icc T (T+1), ∀ s ∈ S,
      1/(2*((S.card : ℝ)+1)) ≤ |t-s| := by
  classical
  let N : ℕ := S.card+1
  let grid (i : Fin N) : ℝ := T+(i.val : ℝ)/(N : ℝ)
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hgrid (i : Fin N) : grid i ∈ Set.Icc T (T+1) := by
    have hi : (i.val : ℝ) < N := by exact_mod_cast i.isLt
    have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    constructor
    · dsimp [grid]
      exact le_add_of_nonneg_right (div_nonneg hi0 hN.le)
    · dsimp [grid]
      have hh : (i.val : ℝ)/(N : ℝ) ≤ 1 := (div_le_one hN).mpr hi.le
      linarith
  by_contra! h
  have hbad : ∀ i : Fin N, ∃ s : S,
      |grid i-(s : ℝ)| < 1/(2*(N : ℝ)) := by
    intro i
    obtain ⟨s, hs, hnear⟩ := h (grid i) (hgrid i)
    exact ⟨⟨s, hs⟩, by simpa only [N, Nat.cast_add, Nat.cast_one] using hnear⟩
  choose f hf using hbad
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp [N])
  have hj := hf j
  rw [← hfij] at hj
  have htriangle : |grid i-grid j| ≤ |grid i-(f i : ℝ)|+|grid j-(f i : ℝ)| := by
    calc
      _ = |(grid i-(f i : ℝ))+((f i : ℝ)-grid j)| := by congr 1; ring
      _ ≤ |grid i-(f i : ℝ)|+|(f i : ℝ)-grid j| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (f i : ℝ) (grid j)]
  have hnear : |grid i-grid j| < 1/(N : ℝ) := by
    have hr : 1/(2*(N : ℝ))+1/(2*(N : ℝ)) = 1/(N : ℝ) := by ring
    linarith [hf i]
  have hdiff : grid i-grid j = ((i.val : ℝ)-(j.val : ℝ))/(N : ℝ) := by
    dsimp [grid]
    ring
  rw [hdiff, abs_div, abs_of_pos hN] at hnear
  have hsmall : |(i.val : ℝ)-(j.val : ℝ)| < 1 :=
    (div_lt_div_iff_of_pos_right hN).mp hnear
  have hne : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
  have hgap : 1 ≤ |(i.val : ℝ)-(j.val : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hi | hj
    · have hh : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast hi
      rw [abs_of_nonpos (by linarith : (i.val : ℝ)-(j.val : ℝ) ≤ 0)]
      linarith
    · have hh : (j.val : ℝ)+1 ≤ i.val := by exact_mod_cast hj
      rw [abs_of_nonneg (by linarith : 0 ≤ (i.val : ℝ)-(j.val : ℝ))]
      linarith
  linarith

theorem exists_height_avoiding_finset_card_le (S : Finset ℝ) (T B : ℝ)
    (hcard : (S.card : ℝ) ≤ B) :
    ∃ t ∈ Set.Icc T (T+1), ∀ s ∈ S, 1/(2*(B+1)) ≤ |t-s| := by
  obtain ⟨t, ht, havoid⟩ := exists_height_avoiding_finset S T
  refine ⟨t, ht, fun s hs => ?_⟩
  apply le_trans _ (havoid s hs)
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  linarith

end ArtinMatthews.VaryingKummerAnalytic
