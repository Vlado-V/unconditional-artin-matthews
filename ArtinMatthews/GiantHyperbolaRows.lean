module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
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

/-! The literal row length after grouping a positive hyperbola by its
cofactor. The reciprocal factor is retained in the norm estimate. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators

theorem giant_hyperbola_sum_by_right {A : Type*} [AddCommMonoid A]
    (X : ℕ) (f : ℕ → ℕ → A) :
    (∑ mn ∈ ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X), f mn.1 mn.2) =
      ∑ n ∈ Ioc 0 X,∑ m ∈ Ioc 0 (X/n), f m n := by
  rw [sum_filter,sum_product,sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext m
  simp only [mem_filter,mem_Ioc]
  have h : m*n ≤ X ↔ m ≤ X/n := (Nat.le_div_iff_mul_le (mem_Ioc.mp hn).1).symm
  constructor
  · exact fun hm => ⟨hm.1.1,h.mp hm.2⟩
  · exact fun hm => ⟨⟨hm.1,hm.2.trans (Nat.div_le_self _ _)⟩,h.mpr hm.2⟩

theorem giant_hyperbola_norm_le (X : ℕ) (A : ℕ → ℕ → ℂ) (β : ℕ → ℂ)
    {D : ℝ} (hD : 0 ≤ D)
    (hA : ∀ m n,0 < m → 0 < n → m*n ≤ X → ‖A m n‖ ≤ D) :
    ‖∑ mn ∈ ((Ioc 0 X)×ˢ(Ioc 0 X)).filter (fun mn => mn.1*mn.2 ≤ X),
      A mn.1 mn.2 * β mn.2‖ ≤ D*(X:ℝ)*(∑ n ∈ Ioc 0 X, ‖β n‖/(n:ℝ)) := by
  rw [giant_hyperbola_sum_by_right X (fun m n => A m n*β n)]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ n ∈ Ioc 0 X, D*(X:ℝ)*(‖β n‖/(n:ℝ)) := by
      apply sum_le_sum
      intro n hn
      have hn₀ := (mem_Ioc.mp hn).1
      calc
        _ ≤ ∑ m ∈ Ioc 0 (X/n),‖A m n*β n‖ := norm_sum_le _ _
        _ ≤ ∑ _m ∈ Ioc 0 (X/n),D*‖β n‖ := by
          apply sum_le_sum
          intro m hm
          rw [norm_mul]
          have hcap := (Nat.le_div_iff_mul_le hn₀).mp (mem_Ioc.mp hm).2
          exact mul_le_mul_of_nonneg_right (hA m n (mem_Ioc.mp hm).1 hn₀ hcap) (norm_nonneg _)
        _ = ((X/n:ℕ):ℝ)*(D*‖β n‖) := by simp only [sum_const,nsmul_eq_mul,Nat.card_Ioc,Nat.sub_zero]
        _ ≤ ((X:ℝ)/n)*(D*‖β n‖) :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (mul_nonneg hD (norm_nonneg _))
        _ = _ := by ring
    _ = _ := (mul_sum ..).symm

end ArtinMatthews
