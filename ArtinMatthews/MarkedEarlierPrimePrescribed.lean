module

public import ArtinMatthews.MarkedPrimeTuplePrefix


set_option backward.privateInPublic true
@[expose] public section

/-! A prescribed prime may depend on the strict earlier tuple and may
be absent. The exact one-coordinate sum is zero for an absent target or
a target outside the actual band; otherwise it is that single atom. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedOptionPrimeRow_sum (P : Finset Nat.Primes) (ν : P → ℝ)
    (target : Option Nat.Primes) :
    (∑ p : P,if some p.1=target then ν p else 0)=
      match target with
      | none => 0
      | some q => if h : q∈P then ν ⟨q,h⟩ else 0 := by
  cases target with
  | none => simp
  | some q =>
    simp only [Option.some.injEq]
    by_cases hq : q∈P
    · rw [dite_eq_left hq]
      calc
        _ = (if (⟨q,hq⟩ : P).1=q then ν ⟨q,hq⟩ else 0) := by
          apply Finset.sum_eq_single (s := Finset.univ)
            (f := fun p : P => if p.1=q then ν p else 0) ⟨q,hq⟩
          · intro p _ hp
            have hn : p.1≠q := fun h => hp (Subtype.ext h)
            exact ite_eq_right hn
          · simp
        _ = _ := ite_eq_left rfl
    · rw [dite_eq_right hq]
      apply Finset.sum_eq_zero
      intro p _
      have hn : p.1≠q := fun h => hq (h ▸ p.2)
      exact ite_eq_right hn

theorem markedOptionPrimeRow_le (P : Finset Nat.Primes) (ν : P → ℝ)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hatom : ∀ p,ν p ≤ Δ) (target : Option Nat.Primes) :
    (∑ p : P,if some p.1=target then ν p else 0) ≤ Δ := by
  rw [markedOptionPrimeRow_sum]
  cases target with
  | none => exact hΔ
  | some q =>
    change (if h : q∈P then ν ⟨q,h⟩ else 0) ≤ Δ
    split_ifs with hq
    · exact hatom ⟨q,hq⟩
    · exact hΔ

variable {n : ℕ} {P : Fin n → Finset Nat.Primes}

def MarkedEarlierPrimeTuplePrescribed (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes)
    (t : (i : Fin n) → ↥(P i)) : Prop :=
  ∀ i∈S,some (t i).1=target i (markedPrimeTuplePrefix t i)

def markedEarlierPrimeKernel (ν : (i : Fin n) → ↥(P i) → ℝ) (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes)
    (i : Fin n) (prior : Fin i.val → Nat.Primes) (p : P i) : ℝ :=
  if i∈S then if some p.1=target i prior then ν i p else 0 else ν i p

theorem markedEarlierPrimeKernel_nonneg (ν : (i : Fin n) → ↥(P i) → ℝ)
    (hν : ∀ i p,0 ≤ ν i p) (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes) :
    ∀ i prior p,0 ≤ markedEarlierPrimeKernel ν S target i prior p := by
  intro i prior p
  unfold markedEarlierPrimeKernel
  split_ifs <;> first | exact hν i p | exact le_rfl

theorem markedEarlierPrimeKernel_row_le (ν : (i : Fin n) → ↥(P i) → ℝ)
    {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hatom : ∀ i p,ν i p ≤ Δ)
    (hmass : ∀ i,(∑ p : P i,ν i p) ≤ N) (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes) :
    ∀ i prior,(∑ p : P i,markedEarlierPrimeKernel ν S target i prior p) ≤ if i∈S then Δ else N := by
  intro i prior
  by_cases hi : i∈S
  · simp only [markedEarlierPrimeKernel,hi,ite_true]
    exact markedOptionPrimeRow_le (P i) (ν i) hΔ (hatom i) (target i prior)
  · simpa only [markedEarlierPrimeKernel,hi,ite_false] using hmass i

theorem markedEarlierPrimeKernel_product (ν : (i : Fin n) → ↥(P i) → ℝ)
    (S : Finset (Fin n))
    (target : (i : Fin n) → (Fin i.val → Nat.Primes) → Option Nat.Primes)
    (t : (i : Fin n) → ↥(P i)) :
    (∏ i,markedEarlierPrimeKernel ν S target i (markedPrimeTuplePrefix t i) (t i))=
      if MarkedEarlierPrimeTuplePrescribed S target t then ∏ i,ν i (t i) else 0 := by
  by_cases ht : MarkedEarlierPrimeTuplePrescribed S target t
  · rw [ite_eq_left ht]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i∈S
    · simp only [markedEarlierPrimeKernel,hi,ht i hi,ite_true]
    · simp only [markedEarlierPrimeKernel,hi,ite_false]
  · rw [ite_eq_right ht]
    unfold MarkedEarlierPrimeTuplePrescribed at ht
    push Not at ht
    obtain ⟨i,hi,hn⟩ := ht
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [markedEarlierPrimeKernel,hi,hn,ite_true,ite_false]

end
end ArtinMatthews
