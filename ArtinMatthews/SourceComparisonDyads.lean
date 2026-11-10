module

public import ArtinMatthews.GiantPrimeNormalization
public import ArtinMatthews.PrimeExtractionDyadicPartition
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite dyads for the small prime, giant prime, and cofactor. -/

namespace ArtinMatthews

open Finset

noncomputable section

def sourceComparisonDyadKey (n : ℕ) : ℕ := Nat.log 2 (n-1)

def sourceComparisonDyadIndices (S : Finset ℕ) : Finset ℕ :=
  S.image sourceComparisonDyadKey

def sourceComparisonDyad (S : Finset ℕ) (j : ℕ) : Finset ℕ :=
  S.filter (fun n => sourceComparisonDyadKey n=j)

def sourceComparisonDyadScale (j : ℕ) : ℕ := 2^j

theorem sourceComparisonDyad_bounds {S : Finset ℕ} {j n : ℕ}
    (hn : n ∈ sourceComparisonDyad S j) (hn₀ : 0 < n) :
    sourceComparisonDyadScale j ≤ n ∧ n ≤ 2*sourceComparisonDyadScale j := by
  have hkey : Nat.log 2 (n-1) = j := (mem_filter.mp hn).2
  by_cases h : n = 1
  · subst n
    have hj : j = 0 := by simpa using hkey.symm
    norm_num [hj, sourceComparisonDyadScale]
  · have hn1 : n-1 ≠ 0 := by omega
    have hlow := Nat.pow_log_le_self 2 hn1
    have hhigh := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (n-1)
    rw [hkey] at hlow hhigh
    simp only [sourceComparisonDyadScale]
    rw [pow_succ, mul_comm] at hhigh
    omega

theorem sourceComparisonDyad_mem_iff {S : Finset ℕ} {j n : ℕ} (hj : 0 < j) :
    n ∈ sourceComparisonDyad S j ↔ n ∈ S ∧
      sourceComparisonDyadScale j < n ∧ n ≤ 2*sourceComparisonDyadScale j := by
  constructor
  · intro hn
    have hkey : Nat.log 2 (n-1) = j := (mem_filter.mp hn).2
    have hn1 : n-1 ≠ 0 := by
      intro h
      rw [h, Nat.log_zero_right] at hkey
      omega
    have hlow := Nat.pow_log_le_self 2 hn1
    rw [hkey] at hlow
    exact ⟨(mem_filter.mp hn).1, by dsimp [sourceComparisonDyadScale]; omega,
      (sourceComparisonDyad_bounds hn (by omega)).2⟩
  · rintro ⟨hS, hlo, hhi⟩
    apply mem_filter.mpr
    refine ⟨hS, ?_⟩
    dsimp [sourceComparisonDyadKey, sourceComparisonDyadScale] at *
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · rw [pow_succ, mul_comm]
      omega

theorem sourceComparisonCofactorDyad_eq (N j : ℕ) (hj : 0 < j) :
    sourceComparisonDyad (Ioc 0 N) j =
      Icc (sourceComparisonDyadScale j+1) (min N (2*sourceComparisonDyadScale j)) := by
  ext n
  rw [sourceComparisonDyad_mem_iff hj, mem_Ioc, mem_Icc, le_min_iff]
  omega

theorem sourceComparisonGiantDyad_eq {x ε : ℝ} (hx : 0 ≤ x) (j : ℕ) (hj : 0 < j) :
    sourceComparisonDyad (giantPrimeWindow x ε) j =
      (Ioc ⌊max (sourceComparisonDyadScale j:ℝ) (x^(1-ε))⌋₊
        ⌊min (2*(sourceComparisonDyadScale j:ℝ)) (x^(1-ε/2))⌋₊).filter Nat.Prime := by
  classical
  ext n
  rw [sourceComparisonDyad_mem_iff hj, mem_giantPrimeWindow hx, mem_filter, mem_Ioc]
  have hu : 0 ≤ max (sourceComparisonDyadScale j:ℝ) (x^(1-ε)) := by positivity
  have hv : 0 ≤ min (2*(sourceComparisonDyadScale j:ℝ)) (x^(1-ε/2)) := by positivity
  rw [Nat.floor_lt hu, Nat.le_floor_iff hv, max_lt_iff, le_min_iff]
  have hlo : sourceComparisonDyadScale j < n ↔
      (sourceComparisonDyadScale j:ℝ) < (n:ℝ) := by norm_cast
  have hhi : n ≤ 2*sourceComparisonDyadScale j ↔
      (n:ℝ) ≤ 2*(sourceComparisonDyadScale j:ℝ) := by norm_cast
  rw [hlo,hhi]
  tauto

theorem sourceComparisonDyadIndices_card (S : Finset ℕ) (Z : ℝ) (hZ : 1 ≤ Z)
    (hS : ∀ n ∈ S, (n:ℝ) ≤ Z) :
    ((sourceComparisonDyadIndices S).card:ℝ) ≤ 1+Real.log (Z+1)/Real.log 2 := by
  classical
  have hsub : sourceComparisonDyadIndices S ⊆ range (Nat.log 2 ⌊Z⌋₊+1) := by
    intro j hj
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hj
    apply mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    exact (Nat.sub_le _ _).trans ((Nat.le_floor_iff (by linarith)).mpr (hS n hn))
  have hc : ((sourceComparisonDyadIndices S).card:ℝ) ≤ (Nat.log 2 ⌊Z⌋₊:ℝ)+1 := by
    exact_mod_cast (card_le_card hsub).trans_eq (card_range _)
  have hb := primeExtractionDyadicIndex_count_le ⌊Z⌋₊
  have hlog : Real.log ((⌊Z⌋₊:ℝ)+1) ≤ Real.log (Z+1) :=
    Real.log_le_log (by positivity) (by linarith [Nat.floor_le (by linarith : 0 ≤ Z)])
  apply hc.trans
  calc
    _ ≤ 1+Real.log ((⌊Z⌋₊:ℝ)+1)/Real.log 2 := by exact_mod_cast hb
    _ ≤ _ := by
      exact add_le_add_right (div_le_div_of_nonneg_right hlog
        (Real.log_nonneg (by norm_num))) 1

end
end ArtinMatthews
