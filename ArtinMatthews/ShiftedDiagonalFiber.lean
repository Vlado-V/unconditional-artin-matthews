module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact representation counting for the diagonal term in §5.3.
Grouping by k=mn+1 costs τ(k-1), rather than the entire m interval.
-/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

def shiftedProductFiber (M T k : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 T)).filter (fun p => p.1*p.2+1=k)

theorem shiftedProductFiber_card_le (M T k : ℕ) :
    (shiftedProductFiber M T k).card ≤ (k-1).divisors.card := by
  by_cases hk : 1<k
  · apply Finset.card_le_card_of_injOn (fun p : ℕ×ℕ => p.1)
    · intro p hp
      obtain ⟨hm,he⟩ := Finset.mem_filter.mp hp
      have he' : k-1=p.1*p.2 := by omega
      exact Nat.mem_divisors.mpr ⟨by rw [he']; exact dvd_mul_right _ _,by omega⟩
    · intro p hp q hq hpq
      change p.1=q.1 at hpq
      obtain ⟨hpbox,hpk⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqbox,hqk⟩ := Finset.mem_filter.mp hq
      have hp₁ : 0<p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hpbox).1).1
      have hprod : p.1*p.2=p.1*q.2 := by rw [hpq] at hpk ⊢; omega
      exact Prod.ext hpq (Nat.eq_of_mul_eq_mul_left hp₁ hprod)
  · have hempty : shiftedProductFiber M T k=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hm,he⟩ := Finset.mem_filter.mp hp
      obtain ⟨hm₁,hm₂⟩ := Finset.mem_product.mp hm
      have hp₁ : 0<p.1 := (Finset.mem_Icc.mp hm₁).1
      have hp₂ : 0<p.2 := (Finset.mem_Icc.mp hm₂).1
      have := Nat.mul_pos hp₁ hp₂
      omega
    simp [hempty]

theorem shiftedProduct_sum_grouped (M T : ℕ) (w : ℕ → ℝ) :
    (∑ m∈Finset.Icc 1 M, ∑ n∈Finset.Icc 1 T, w (m*n+1)) =
      ∑ k∈Finset.Icc 2 (M*T+1), ((shiftedProductFiber M T k).card : ℝ)*w k := by
  have hh := Finset.sum_fiberwise_of_maps_to
    (s:=(Finset.Icc 1 M) ×ˢ (Finset.Icc 1 T))
    (t:=Finset.Icc 2 (M*T+1)) (g:=fun p : ℕ×ℕ => p.1*p.2+1)
    (fun p hp => by
      obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hp
      obtain ⟨hl₁,hu₁⟩ := Finset.mem_Icc.mp hp₁
      obtain ⟨hl₂,hu₂⟩ := Finset.mem_Icc.mp hp₂
      apply Finset.mem_Icc.mpr
      constructor
      · have := Nat.mul_pos hl₁ hl₂; omega
      · exact Nat.add_le_add_right (Nat.mul_le_mul hu₁ hu₂) 1)
    (fun p : ℕ×ℕ => w (p.1*p.2+1))
  rw [← Finset.sum_product (Finset.Icc 1 M) (Finset.Icc 1 T)
    (fun p : ℕ×ℕ => w (p.1*p.2+1)),← hh]
  apply Finset.sum_congr rfl
  intro k _hk
  change (∑ p∈shiftedProductFiber M T k, w (p.1*p.2+1)) = _
  calc
    _ = ∑ _p∈shiftedProductFiber M T k, w k := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

/-- Nonnegative diagonal weights incur precisely a divisor multiplicity. -/
theorem shiftedProduct_sum_le_divisors (M T : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k, 0≤w k) :
    (∑ m∈Finset.Icc 1 M, ∑ n∈Finset.Icc 1 T, w (m*n+1)) ≤
      ∑ k∈Finset.Icc 2 (M*T+1), ((k-1).divisors.card : ℝ)*w k := by
  rw [shiftedProduct_sum_grouped]
  apply Finset.sum_le_sum
  intro k _hk
  apply mul_le_mul_of_nonneg_right _ (hw k)
  exact_mod_cast shiftedProductFiber_card_le M T k

end ArtinMatthews
