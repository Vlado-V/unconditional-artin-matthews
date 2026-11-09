module

public import ArtinMatthews.MarkedMemoryFiniteLabelOrbit
public import ArtinMatthews.MarkedMemoryFiniteAnchorNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized finite-tableau label orbit is free and has exactly
the product of factorials of the supplied particle counts. This counts
the constructed orbit, without postulating transitivity of a history
fiber or discarding any additional admissibility requirements. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hn : MarkedMemoryBirthNormalized hZ d)

def markedMemoryNormalizedFiniteRelabel (e : (j : J) → Equiv.Perm (A j)) :
    MarkedMemoryNormalizedFiniteTableau (A := A) (P := P) (pads := pads) (B := B) (n := n) hZ :=
  markedMemoryIndependent_toNormalizedFinite hZ (markedMemoryIndependentRelabel hZ e d)
    (markedMemoryBirthNormalized_relabel hZ d hn e)

theorem markedMemoryNormalizedFiniteRelabel_val (e : (j : J) → Equiv.Perm (A j)) :
    (markedMemoryNormalizedFiniteRelabel hZ d hn e).1=markedMemoryFiniteRelabel hZ d e := rfl

theorem markedMemoryNormalizedFiniteRelabel_injective :
    Function.Injective (markedMemoryNormalizedFiniteRelabel hZ d hn) := by
  intro e f h
  exact markedMemoryFiniteRelabel_injective hZ d (congrArg Subtype.val h)

theorem markedMemoryNormalizedFiniteRelabel_history_heq (e : (j : J) → Equiv.Perm (A j))
    (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ
        (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryNormalizedFiniteRelabel hZ d hn e).1) order)
      (markedMemoryIndependentHistory hZ d order) :=
  markedMemoryFiniteRelabel_history_heq hZ d e order

def markedMemoryNormalizedLabelOrbit := Set.range (markedMemoryNormalizedFiniteRelabel hZ d hn)

def markedMemoryNormalizedLabelOrbitEquiv :
    ((j : J) → Equiv.Perm (A j)) ≃ markedMemoryNormalizedLabelOrbit hZ d hn :=
  Equiv.ofInjective _ (markedMemoryNormalizedFiniteRelabel_injective hZ d hn)

instance markedMemoryNormalizedLabelOrbit_fintype : Fintype (markedMemoryNormalizedLabelOrbit hZ d hn) :=
  Fintype.ofEquiv ((j : J) → Equiv.Perm (A j)) (markedMemoryNormalizedLabelOrbitEquiv hZ d hn)

theorem markedMemoryNormalizedLabelOrbit_card :
    Fintype.card (markedMemoryNormalizedLabelOrbit hZ d hn)=∏ j,(Fintype.card (A j)).factorial := by
  rw [← Fintype.card_congr (markedMemoryNormalizedLabelOrbitEquiv hZ d hn)]
  simp only [Fintype.card_pi,Fintype.card_perm]

theorem markedMemoryNormalizedLabelOrbit_history_heq
    (f : markedMemoryNormalizedLabelOrbit hZ d hn) (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ (markedMemoryFiniteTableau_toIndependent hZ f.1.1) order)
      (markedMemoryIndependentHistory hZ d order) := by
  obtain ⟨e,he⟩ := f.2
  rw [← he]
  exact markedMemoryNormalizedFiniteRelabel_history_heq hZ d hn e order

end
end ArtinMatthews
