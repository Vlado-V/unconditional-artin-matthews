module

public import ArtinMatthews.MarkedOrderedPrimeReindex


set_option backward.privateInPublic true
@[expose] public section

/-! The exact earlier-dependent prime mass estimate on any actual finite
linearly ordered carrier. Its increasing enumeration is constructed from
the order, rather than supplied as an additional reindexing hypothesis. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A : Type*} [LinearOrder A] [Fintype A]

theorem markedOrderedPrimeTuple_sum_le_of_orderIso {n : ℕ} (e : Fin n ≃o A)
    {P : A → Finset Nat.Primes} (ν : (a : A) → ↥(P a) → ℝ)
    (hν : ∀ a p,0 ≤ ν a p) {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 0 ≤ N)
    (hatom : ∀ a p,ν a p ≤ Δ) (hmass : ∀ a,(∑ p : P a,ν a p) ≤ N)
    (S : Finset A)
    (target : (a : A) → ({b : A // b<a} → Nat.Primes) → Option Nat.Primes) :
    (∑ t : (a : A) → ↥(P a),
      if MarkedOrderedPrimeTuplePrescribed S target t then ∏ a,ν a (t a) else 0) ≤
      Δ^S.card*N^(n-S.card) := by
  let E := Equiv.piCongrLeft (fun a => ↥(P a)) e.toEquiv
  have he : (∑ t : (a : A) → ↥(P a),
      if MarkedOrderedPrimeTuplePrescribed S target t then ∏ a,ν a (t a) else 0)=
      ∑ t : (i : Fin n) → ↥(P (e i)),
        if MarkedEarlierPrimeTuplePrescribed (markedOrderedPrimeSelected e S)
            (markedOrderedPrimeTarget e target) t then ∏ i,ν (e i) (t i) else 0 := by
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [E]
    rw [markedOrderedPrimePrescribed_reindex,markedOrderedPrimeProduct_reindex]
  rw [he]
  simpa only [markedOrderedPrimeSelected_card] using
    markedEarlierPrimeTuple_sum_le (fun i => ν (e i)) (fun i => hν (e i)) hΔ hN
      (fun i => hatom (e i)) (fun i => hmass (e i))
      (markedOrderedPrimeSelected e S) (markedOrderedPrimeTarget e target)

theorem markedOrderedPrimeTuple_sum_le {P : A → Finset Nat.Primes}
    (ν : (a : A) → ↥(P a) → ℝ) (hν : ∀ a p,0 ≤ ν a p)
    {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 0 ≤ N)
    (hatom : ∀ a p,ν a p ≤ Δ) (hmass : ∀ a,(∑ p : P a,ν a p) ≤ N)
    (S : Finset A)
    (target : (a : A) → ({b : A // b<a} → Nat.Primes) → Option Nat.Primes) :
    (∑ t : (a : A) → ↥(P a),
      if MarkedOrderedPrimeTuplePrescribed S target t then ∏ a,ν a (t a) else 0) ≤
      Δ^S.card*N^(Fintype.card A-S.card) :=
  markedOrderedPrimeTuple_sum_le_of_orderIso (Fintype.orderIsoFinOfCardEq A rfl)
    ν hν hΔ hN hatom hmass S target

theorem markedOrderedPrimeTuple_sum_le_slack {P : A → Finset Nat.Primes}
    (ν : (a : A) → ↥(P a) → ℝ) (hν : ∀ a p,0 ≤ ν a p)
    {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 1 ≤ N)
    (hatom : ∀ a p,ν a p ≤ Δ) (hmass : ∀ a,(∑ p : P a,ν a p) ≤ N)
    (S : Finset A)
    (target : (a : A) → ({b : A // b<a} → Nat.Primes) → Option Nat.Primes) :
    (∑ t : (a : A) → ↥(P a),
      if MarkedOrderedPrimeTuplePrescribed S target t then ∏ a,ν a (t a) else 0) ≤
      Δ^S.card*N^(Fintype.card A) := by
  refine (markedOrderedPrimeTuple_sum_le ν hν hΔ (zero_le_one.trans hN) hatom hmass S target).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN (Nat.sub_le (Fintype.card A) S.card))
    (pow_nonneg hΔ _)

def markedOrderedPrimeParentTarget
    (parent : (a : A) → Option {b : A // b<a}) (old : A → Option Nat.Primes)
    (a : A) (prior : {b : A // b<a} → Nat.Primes) : Option Nat.Primes :=
  match parent a with
  | some b => some (prior b)
  | none => old a

theorem markedOrderedPrimeParentTuple_sum_le {P : A → Finset Nat.Primes}
    (ν : (a : A) → ↥(P a) → ℝ) (hν : ∀ a p,0 ≤ ν a p)
    {Δ N : ℝ} (hΔ : 0 ≤ Δ) (hN : 0 ≤ N)
    (hatom : ∀ a p,ν a p ≤ Δ) (hmass : ∀ a,(∑ p : P a,ν a p) ≤ N)
    (S : Finset A) (parent : (a : A) → Option {b : A // b<a})
    (old : A → Option Nat.Primes) :
    (∑ t : (a : A) → ↥(P a),
      if MarkedOrderedPrimeTuplePrescribed S (markedOrderedPrimeParentTarget parent old) t
      then ∏ a,ν a (t a) else 0) ≤ Δ^S.card*N^(Fintype.card A-S.card) :=
  markedOrderedPrimeTuple_sum_le ν hν hΔ hN hatom hmass S _

end
end ArtinMatthews
