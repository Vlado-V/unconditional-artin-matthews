module

public import ArtinMatthews.MarkedMemoryLabelOrbit
public import ArtinMatthews.MarkedMemoryFiniteHistory
public import ArtinMatthews.MarkedMemoryIndependentRelabelHistory


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine finite time wrapper retains the free label action. Each
orbit has the factorial number of distinct finite tableaux and every
member assembles to the same literal history. No assertion that this
orbit exhausts an unrestricted history fiber is made. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

def markedMemoryFiniteRelabel (e : (j : J) → Equiv.Perm (A j)) :
    MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n :=
  markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e d)

theorem markedMemoryFiniteRelabel_injective :
    Function.Injective (markedMemoryFiniteRelabel hZ d) := by
  intro e f h
  have hr := congrArg (markedMemoryFiniteTableau_toIndependent hZ) h
  have he : (fun j => (e j : A j → A j))=(fun j => (f j : A j → A j)) := by
    apply markedMemoryIndependent_labelMap_ext hZ d
    · intro v hv j k
      have hh := congrArg (fun z : MarkedMemoryIndependentLifespans
        (A := A) (P := P) (pads := pads) (B := B) hZ n => z.activeId v j k) hr
      simpa only [markedMemoryFiniteRelabel,
        markedMemoryFinite_restore_activeId hZ _ v hv j,markedMemoryIndependentRelabel,
        Function.Embedding.trans_apply,Equiv.toEmbedding_apply] using hh
    · intro t ht j
      have hh := congrArg (fun z : MarkedMemoryIndependentLifespans
        (A := A) (P := P) (pads := pads) (B := B) hZ n => markedMemoryIndependentQueue hZ z t j) hr
      simpa only [markedMemoryFiniteRelabel,markedMemoryFinite_restore_queue hZ _ t ht j,
        markedMemoryIndependentRelabel_queue] using hh
  funext j
  exact Equiv.ext (fun a => congrFun (congrFun he j) a)

theorem markedMemoryFiniteRelabel_history_heq (e : (j : J) → Equiv.Perm (A j))
    (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ
        (markedMemoryFiniteTableau_toIndependent hZ (markedMemoryFiniteRelabel hZ d e)) order)
      (markedMemoryIndependentHistory hZ d order) :=
  (markedMemoryFinite_restore_history_heq hZ (markedMemoryIndependentRelabel hZ e d) order).trans
    (markedMemoryIndependentRelabel_history_heq hZ e d order)

def markedMemoryFiniteLabelOrbit := Set.range (markedMemoryFiniteRelabel hZ d)

def markedMemoryFiniteLabelOrbitEquiv :
    ((j : J) → Equiv.Perm (A j)) ≃ markedMemoryFiniteLabelOrbit hZ d :=
  Equiv.ofInjective _ (markedMemoryFiniteRelabel_injective hZ d)

instance markedMemoryFiniteLabelOrbit_fintype : Fintype (markedMemoryFiniteLabelOrbit hZ d) :=
  Fintype.ofEquiv ((j : J) → Equiv.Perm (A j)) (markedMemoryFiniteLabelOrbitEquiv hZ d)

theorem markedMemoryFiniteLabelOrbit_card :
    Fintype.card (markedMemoryFiniteLabelOrbit hZ d)=∏ j,(Fintype.card (A j)).factorial := by
  rw [← Fintype.card_congr (markedMemoryFiniteLabelOrbitEquiv hZ d)]
  simp only [Fintype.card_pi,Fintype.card_perm]

theorem markedMemoryFiniteLabelOrbit_history_heq
    (f : markedMemoryFiniteLabelOrbit hZ d) (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ (markedMemoryFiniteTableau_toIndependent hZ f.1) order)
      (markedMemoryIndependentHistory hZ d order) := by
  obtain ⟨e,he⟩ := f.2
  rw [← he]
  exact markedMemoryFiniteRelabel_history_heq hZ d e order

theorem markedMemoryFiniteLabelOrbit_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n → R) :
    (∑ e : (j : J) → Equiv.Perm (A j),F (markedMemoryFiniteRelabel hZ d e)) =
      ∑ z : markedMemoryFiniteLabelOrbit hZ d,F z.1 :=
  Equiv.sum_comp (markedMemoryFiniteLabelOrbitEquiv hZ d) (fun z => F z.1)

end
end ArtinMatthews
