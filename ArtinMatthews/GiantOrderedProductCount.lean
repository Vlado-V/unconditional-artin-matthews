module

public import ArtinMatthews.GiantOrderedProductTuples
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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

/-! A harmonic count of all ordered positive tuples under a product cap. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators

private theorem giant_ordered_product_count_step (k X : ℕ) :
    (giantOrderedProductTuples (k+1) X).card ≤
      ∑ a ∈ Ioc 0 X, (giantOrderedProductTuples k (X/a)).card := by
  rw [← card_sigma]
  let f (t : Fin (k+1) → ℕ) : Σ _ : ℕ,Fin k → ℕ := ⟨t 0,Fin.tail t⟩
  apply card_le_card_of_injOn f
  · intro t ht
    obtain ⟨ht₀,hX⟩ := mem_giantOrderedProductTuples.mp ht
    have hp : 0 < ∏ i,t i := prod_pos (fun i _ => ht₀ i)
    have ha : t 0 ≤ X := (Nat.le_of_dvd hp (dvd_prod_of_mem t (mem_univ 0))).trans hX
    have htail : (∏ i,Fin.tail t i) ≤ X/t 0 := by
      apply (Nat.le_div_iff_mul_le (ht₀ 0)).mpr
      rw [Nat.mul_comm]
      exact (Fin.prod_univ_succ t).symm.trans_le hX
    exact mem_sigma.mpr ⟨mem_Ioc.mpr ⟨ht₀ 0,ha⟩,
      mem_giantOrderedProductTuples.mpr ⟨fun i => ht₀ i.succ,htail⟩⟩
  · intro t _ u _ h
    have he := congrArg (fun p : Σ _ : ℕ,Fin k → ℕ =>
      Fin.cons (α := fun _ : Fin (k+1) => ℕ) p.1 p.2) h
    simpa only [f,Fin.cons_self_tail] using he

theorem giant_ordered_product_count_le (k X : ℕ) :
    ((giantOrderedProductTuples k X).card:ℝ) ≤ (X:ℝ)*(1+Real.log (X:ℝ))^k := by
  induction k generalizing X with
  | zero =>
      simp only [pow_zero,mul_one]
      by_cases h : X=0
      · subst X
        have hzero : giantOrderedProductTuples 0 0 = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro t ht
          have hbad := (mem_giantOrderedProductTuples.mp ht).2
          simp only [Fin.prod_univ_zero] at hbad
          omega
        simp only [hzero,card_empty,Nat.cast_zero,le_refl]
      · have hcard : (giantOrderedProductTuples 0 X).card ≤ 1 := by
          apply card_le_one.mpr
          intro t _ u _
          funext i
          exact i.elim0
        exact_mod_cast hcard.trans (Nat.one_le_iff_ne_zero.mpr h)
  | succ k ih =>
      have hharm : (∑ a ∈ Ioc 0 X,(a:ℝ)⁻¹) ≤ 1+Real.log (X:ℝ) := by
        have he : Ioc 0 X = Icc 1 X := by
          ext a
          simp only [mem_Ioc,mem_Icc]
          omega
        rw [he]
        simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
          using harmonic_le_one_add_log X
      have hL : 0 ≤ 1+Real.log (X:ℝ) := by positivity
      calc
        _ ≤ ∑ a ∈ Ioc 0 X, ((giantOrderedProductTuples k (X/a)).card:ℝ) := by
          exact_mod_cast giant_ordered_product_count_step k X
        _ ≤ ∑ a ∈ Ioc 0 X, ((X:ℝ)/a)*(1+Real.log (X:ℝ))^k := by
          apply sum_le_sum
          intro a ha
          obtain ⟨ha₀,haX⟩ := mem_Ioc.mp ha
          have hdiv : 0 < ((X/a:ℕ):ℝ) := by exact_mod_cast Nat.div_pos haX ha₀
          have hlog := Real.log_le_log hdiv (Nat.cast_le.mpr (Nat.div_le_self X a))
          exact (ih (X/a)).trans (mul_le_mul Nat.cast_div_le
            (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hlog) k)
            (by positivity) (by positivity))
        _ = ((X:ℝ)*(1+Real.log (X:ℝ))^k) * ∑ a ∈ Ioc 0 X,(a:ℝ)⁻¹ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro a _
          ring
        _ ≤ ((X:ℝ)*(1+Real.log (X:ℝ))^k)*(1+Real.log (X:ℝ)) :=
          mul_le_mul_of_nonneg_left hharm (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hL _))
        _ = _ := by rw [pow_succ,mul_assoc]

end ArtinMatthews
