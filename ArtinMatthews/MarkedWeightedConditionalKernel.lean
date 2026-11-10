module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! Positive conditional row iteration. These are finite sum identities
and inequalities; actual chronological rows supply all row bounds. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedWeightedConditionalKernel_bound {I : Type*} [Fintype I]
    (K W f : I → ℝ) {w₀ C R : ℝ} (hw₀ : 0 < w₀) (hC : 0 ≤ C)
    (hK : ∀ i,0 ≤ K i) (hf : ∀ i,f i ≤ C*W i)
    (hrow : (∑ i,K i*W i/w₀) ≤ R) :
    (∑ i,K i*f i) ≤ C*R*w₀ := by
  calc
    _ ≤ ∑ i,K i*(C*W i) := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hK i))
    _ = C*(∑ i,K i*W i/w₀)*w₀ := by
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrow hC) hw₀.le

def markedConditionalWordBudget (g e : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,j => g j
  | n+1,j => g j*(e j*markedConditionalWordBudget g e n (j+1))

theorem markedConditionalWordBudget_nonneg (g e : ℕ → ℝ)
    (hg : ∀ j,0 ≤ g j) (he : ∀ j,0 ≤ e j) (n j : ℕ) :
    0 ≤ markedConditionalWordBudget g e n j := by
  induction n generalizing j with
  | zero => exact hg j
  | succ n ih => exact mul_nonneg (hg j) (mul_nonneg (he j) (ih (j+1)))

def markedConditionalWord {A S : Type*}
    (ghost edge : ℕ → (A → S → ℝ) → A → S → ℝ) :
    ℕ → ℕ → (A → S → ℝ) → A → S → ℝ
  | 0,j,f => ghost j f
  | n+1,j,f => ghost j (edge j (markedConditionalWord ghost edge n (j+1) f))

theorem markedConditionalWord_bound {A S : Type*}
    (ghost edge : ℕ → (A → S → ℝ) → A → S → ℝ)
    (g e : ℕ → ℝ) (w : S → ℝ) (hg : ∀ j,0 ≤ g j) (he : ∀ j,0 ≤ e j)
    (hghost : ∀ j (F : A → S → ℝ) (C : ℝ), 0 ≤ C →
      (∀ a s,F a s ≤ C*w s) → ∀ a s,ghost j F a s ≤ C*g j*w s)
    (hedge : ∀ j (F : A → S → ℝ) (C : ℝ), 0 ≤ C →
      (∀ a s,F a s ≤ C*w s) → ∀ a s,edge j F a s ≤ C*e j*w s)
    (f : A → S → ℝ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ a s,f a s ≤ C*w s)
    (n j : ℕ) (a : A) (s : S) :
    markedConditionalWord ghost edge n j f a s ≤
      C*markedConditionalWordBudget g e n j*w s := by
  induction n generalizing j a s with
  | zero => exact hghost j f C hC hf a s
  | succ n ih =>
    have htail : ∀ a s,markedConditionalWord ghost edge n (j+1) f a s ≤
        (C*markedConditionalWordBudget g e n (j+1))*w s :=
      fun a s => ih (j+1) a s
    have hc : 0 ≤ C*markedConditionalWordBudget g e n (j+1) :=
      mul_nonneg hC (markedConditionalWordBudget_nonneg g e hg he n (j+1))
    have hedge' := hedge j (markedConditionalWord ghost edge n (j+1) f)
      (C*markedConditionalWordBudget g e n (j+1)) hc htail
    have hc' : 0 ≤ C*markedConditionalWordBudget g e n (j+1)*e j := mul_nonneg hc (he j)
    have hh := hghost j (edge j (markedConditionalWord ghost edge n (j+1) f))
      (C*markedConditionalWordBudget g e n (j+1)*e j) hc' hedge' a s
    exact hh.trans_eq (by dsimp [markedConditionalWord,markedConditionalWordBudget]; ring)

end ArtinMatthews
