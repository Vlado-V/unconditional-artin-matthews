module

public import ArtinMatthews.MarkedMemoryPrimeLifespanChoices


set_option backward.privateInPublic true
@[expose] public section

/-! A finite weighted counting inequality for literal choice costs.
Its later orphan specialization keeps the actual source memory cutoff;
no change to a full-band memory bound is involved. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] {C : I → Type*} [∀ i,Fintype (C i)]

def markedMemoryChoiceCount (cost : (i : I) → C i → ℕ) (c : (i : I) → C i) : ℕ :=
  ∑ i,cost i (c i)

theorem markedMemoryChoiceCount_generating
    (cost : (i : I) → C i → ℕ) (w : (i : I) → C i → ℝ) (r : ℝ) :
    (∑ c : (i : I) → C i,r ^ markedMemoryChoiceCount cost c * ∏ i,w i (c i)) =
      ∏ i,∑ a : C i,r ^ cost i a * w i a := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rfl

theorem markedMemoryChoiceCount_tail_mul
    (cost : (i : I) → C i → ℕ) (w : (i : I) → C i → ℝ)
    (hw : ∀ i a,0≤w i a) (r : ℝ) (hr : 1≤r) (m : ℕ) :
    r^m * (∑ c : (i : I) → C i,
      if m ≤ markedMemoryChoiceCount cost c then ∏ i,w i (c i) else 0) ≤
      ∏ i,∑ a : C i,r ^ cost i a * w i a := by
  rw [← markedMemoryChoiceCount_generating cost w r,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  have hp : 0≤∏ i,w i (c i) := Finset.prod_nonneg (fun i _ => hw i (c i))
  by_cases hc : m ≤ markedMemoryChoiceCount cost c
  · simp only [hc,ite_true]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr hc) hp
  · simp only [hc,ite_false,mul_zero]
    exact mul_nonneg (pow_nonneg (by linarith) _) hp

theorem markedMemoryChoiceCount_tail
    (cost : (i : I) → C i → ℕ) (w : (i : I) → C i → ℝ)
    (hw : ∀ i a,0≤w i a) (r : ℝ) (hr : 1≤r) (m : ℕ) :
    (∑ c : (i : I) → C i,
      if m ≤ markedMemoryChoiceCount cost c then ∏ i,w i (c i) else 0) ≤
      (∏ i,∑ a : C i,r ^ cost i a * w i a)/r^m := by
  have hp : 0<r^m := pow_pos (by linarith) _
  apply (le_div_iff₀ hp).mpr
  simpa only [mul_comm] using markedMemoryChoiceCount_tail_mul cost w hw r hr m

end
end ArtinMatthews
