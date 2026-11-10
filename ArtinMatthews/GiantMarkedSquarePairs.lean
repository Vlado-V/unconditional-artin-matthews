module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.ModEq
public import ArtinMatthews.MarkedProgressionCounting
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rectangle pairs with a marking prime square dividing the
predecessor. Each row for a fixed modulus lies in one residue class. -/

noncomputable section
namespace ArtinMatthews

def giantMarkedSquareRow (U : Finset ℕ) (m : ℕ) (N : Finset ℕ) : Finset ℕ := by
  classical
  exact N.filter fun n => ∃ p ∈ U, p ^ 2 ∣ m * n - 1

def giantMarkedSquareCount (U M N : Finset ℕ) : ℕ :=
  ∑ m ∈ M, (giantMarkedSquareRow U m N).card

theorem giantMarkedPredecessor_modEq {m n d : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hd : d ∣ m * n - 1) : Nat.ModEq d (m * n) 1 := by
  have h := (Nat.modEq_zero_iff_dvd.mpr hd).add_right 1
  simpa only [Nat.sub_add_cancel (Nat.mul_pos hm hn), zero_add] using h

theorem giantMarkedPredecessor_row_modEq {m n k d : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k)
    (hnd : d ∣ m * n - 1) (hkd : d ∣ m * k - 1) : Nat.ModEq d n k := by
  calc
    n = 1 * n := (one_mul n).symm
    _ ≡ (m * k) * n [MOD d] := ((giantMarkedPredecessor_modEq hm hk hkd).mul_right n).symm
    _ = (m * n) * k := by ac_rfl
    _ ≡ 1 * k [MOD d] := (giantMarkedPredecessor_modEq hm hn hnd).mul_right k
    _ = k := one_mul k

theorem giantMarkedPredecessor_row_card_le (N : Finset ℕ) {m d : ℕ} {H : ℝ}
    (hm : 0 < m) (hd : 0 < d) (hdH : (d : ℝ) ≤ H)
    (hN : ∀ n ∈ N, 0 < n ∧ (n : ℝ) ≤ 2 * H) :
    (((N.filter fun n => d ∣ m * n - 1).card : ℕ) : ℝ) ≤ 3 * H / d := by
  classical
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hH := hd0.trans_le hdH
  let R := N.filter fun n => d ∣ m * n - 1
  change (R.card : ℝ) ≤ _
  by_cases hR : R.Nonempty
  · obtain ⟨k, hk⟩ := hR
    obtain ⟨hkN, hkd⟩ := Finset.mem_filter.mp hk
    let b : ℕ := ⌊2 * H⌋₊
    have hsub : R ⊆ (Finset.Ioc 0 b).filter (fun n => Nat.ModEq d n k) := by
      intro n hn
      obtain ⟨hnN, hnd⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨(hN n hnN).1,
          (Nat.le_floor_iff (by positivity : 0 ≤ 2 * H)).mpr (hN n hnN).2⟩,
        giantMarkedPredecessor_row_modEq hm (hN n hnN).1 (hN k hkN).1 hnd hkd⟩
    have hcount := marked_interval_residue_error 0 b d k (Nat.zero_le _) hd
    rw [abs_le] at hcount
    have hb : (b : ℝ) ≤ 2 * H := Nat.floor_le (by positivity)
    have hc : (R.card : ℝ) ≤ (((Finset.Ioc 0 b).filter
        (fun n => Nat.ModEq d n k)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    calc
      _ ≤ (b : ℝ) / d + 1 := by
        have hu := hcount.2
        simp only [Nat.cast_zero, sub_zero] at hu
        linarith
      _ ≤ _ := by
        apply (le_div_iff₀ hd0).mpr
        rw [add_mul, div_mul_cancel₀ _ hd0.ne', one_mul]
        linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hR]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem giantMarkedSquareCount_le (U M N : Finset ℕ) {Hm Hn : ℝ}
    (hHm : 1 ≤ Hm) (hHn : 1 ≤ Hn)
    (hM : ∀ m ∈ M, 0 < m ∧ (m : ℝ) ≤ 2 * Hm)
    (hN : ∀ n ∈ N, 0 < n ∧ (n : ℝ) ≤ 2 * Hn)
    (hU : ∀ p ∈ U, 0 < p ∧ (p : ℝ) ^ 2 ≤ Hn) :
    (giantMarkedSquareCount U M N : ℝ) ≤
      9 * Hm * Hn * ∑ p ∈ U, 1 / (p : ℝ) ^ 2 := by
  classical
  let R := ∑ p ∈ U, 1 / (p : ℝ) ^ 2
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => by positivity)
  have hmCard : (M.card : ℝ) ≤ 3 * Hm := by
    let b : ℕ := ⌊2 * Hm⌋₊
    have hb : (b : ℝ) ≤ 2 * Hm := Nat.floor_le (by linarith)
    have hsub : M ⊆ Finset.range (b + 1) := by
      intro m hm
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le ((Nat.le_floor_iff (by linarith : 0 ≤ 2 * Hm)).mpr (hM m hm).2)
    have hc : (M.card : ℝ) ≤ (b : ℝ) + 1 := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    linarith
  have hrow : ∀ m ∈ M, ((giantMarkedSquareRow U m N).card : ℝ) ≤ 3 * Hn * R := by
    intro m hm
    let Q (p : ℕ) := N.filter fun n => p ^ 2 ∣ m * n - 1
    have hset : giantMarkedSquareRow U m N = U.biUnion Q := by
      ext n
      simp only [giantMarkedSquareRow, Finset.mem_filter, Finset.mem_biUnion, Q]
      tauto
    have hc : ((U.biUnion Q).card : ℝ) ≤ ∑ p ∈ U, ((Q p).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    calc
      _ ≤ ∑ p ∈ U, ((Q p).card : ℝ) := hset ▸ hc
      _ ≤ ∑ p ∈ U, 3 * Hn / (p : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hp2 : ((p ^ 2 : ℕ) : ℝ) ≤ Hn := by simpa only [Nat.cast_pow] using (hU p hp).2
        simpa only [Q, Nat.cast_pow] using
          giantMarkedPredecessor_row_card_le N (hM m hm).1 (pow_pos (hU p hp).1 _) hp2 hN
      _ = 3 * Hn * R := by
        change _ = 3 * Hn * ∑ p ∈ U, 1 / (p : ℝ) ^ 2
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _hp
        ring
  rw [giantMarkedSquareCount, Nat.cast_sum]
  calc
    _ ≤ ∑ _m ∈ M, 3 * Hn * R := Finset.sum_le_sum hrow
    _ = (M.card : ℝ) * (3 * Hn * R) := by simp
    _ ≤ (3 * Hm) * (3 * Hn * R) := mul_le_mul_of_nonneg_right hmCard (by positivity)
    _ = _ := by ring

end ArtinMatthews
