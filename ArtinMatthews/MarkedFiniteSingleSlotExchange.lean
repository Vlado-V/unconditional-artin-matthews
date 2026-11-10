module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Tactic.Finiteness.Attr


set_option backward.privateInPublic true
@[expose] public section

/-! A shared literal prefix gives the exact one-slot exchange, including
after two independent permutations of the endpoint lists. -/
namespace ArtinMatthews

theorem markedPermutedRange_iff {α : Type*} {m : ℕ}
    (a : Fin m → α) (σ : Equiv.Perm (Fin m)) (x : α) :
    (∃ k,a (σ k)=x) ↔ ∃ k,a k=x := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨σ k,hk⟩
  · rintro ⟨k,hk⟩; exact ⟨σ.symm k,by simpa only [Equiv.apply_symm_apply] using hk⟩

theorem markedSingleSlotExchange {α : Type*} (pads : ℕ)
    (a b : Fin (pads+1) → α) (ha : Function.Injective a)
    (hcopy : ∀ k : Fin pads,a k.castSucc=b k.castSucc) (x : α) :
    (∃ k,b k=x) ↔ ((∃ k,a k=x) ∧ x≠a (Fin.last pads)) ∨ x=b (Fin.last pads) := by
  constructor
  · rintro ⟨k,hk⟩
    cases k using Fin.lastCases with
    | last => exact Or.inr hk.symm
    | cast k =>
      refine Or.inl ⟨⟨k.castSucc,(hcopy k).trans hk⟩,?_⟩
      intro hx
      exact Fin.castSucc_ne_last k (ha ((hcopy k).trans (hk.trans hx)))
  · rintro (⟨⟨k,hk⟩,hne⟩ | hi)
    · cases k using Fin.lastCases with
      | last => exact False.elim (hne hk.symm)
      | cast k => exact ⟨k.castSucc,(hcopy k).symm.trans hk⟩
    · exact ⟨Fin.last pads,hi.symm⟩

theorem markedPermutedSingleSlotExchange {α : Type*} (pads : ℕ)
    (a b : Fin (pads+1) → α) (ha : Function.Injective a)
    (σ τ : Equiv.Perm (Fin (pads+1)))
    (hcopy : ∀ k : Fin pads,a (σ k.castSucc)=b (τ k.castSucc)) (x : α) :
    (∃ k,b k=x) ↔
      ((∃ k,a k=x) ∧ x≠a (σ (Fin.last pads))) ∨ x=b (τ (Fin.last pads)) := by
  have h := markedSingleSlotExchange pads (fun k => a (σ k)) (fun k => b (τ k))
    (ha.comp σ.injective) hcopy x
  simpa only [markedPermutedRange_iff] using h

end ArtinMatthews
