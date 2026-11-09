module

public import ArtinMatthews.MarkedMemoryIndependentCappedIndex
public import ArtinMatthews.MarkedMemoryIndependentCappedBirths
public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedMemoryFiniteHistory
public import ArtinMatthews.MarkedMemoryIndependentRelabelHistory


set_option backward.privateInPublic true
@[expose] public section

/-! Reconstructing the capped path and all its literal decorations from
an independent tableau gives the same original chronological history.
The relabeling is the derived used-prime equivalence. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

theorem markedMemoryIndependentHistory_congr_heq
    {A : J → Type*} [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
    {d e : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n}
    (he : d=e) (order : Fin n → J → Equiv.Perm (Fin pads)) :
    HEq (markedMemoryIndependentHistory hZ d order) (markedMemoryIndependentHistory hZ e order) := by
  cases he
  rfl

variable {A : J → Type*} [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))
  (hempty : ∀ j,(d.lifespan j).initial=[])
  (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
  (hn : MarkedMemoryBirthNormalized hZ d)
  (order : Fin n → J → Equiv.Perm (Fin pads))
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ d order))
  (s : MarkedRawState P (pads+1) B Z)
  (hs : markedMemoryIndependentState hZ d 0 (Nat.zero_le n)=s)

def markedMemoryIndependentCappedLift : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s :=
  ⟨markedMemoryIndependentCappedPathIndex hZ d hinj hempty hterminal hn order ha s hs,
    markedMemoryIndependentCappedBirths hZ d hinj hempty hterminal hn order ha,order⟩

theorem markedMemoryIndependentCappedLift_history_heq
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j)) :
    HEq (markedMemoryCappedPathDecoratedAssembly hZ hP s
      (markedMemoryIndependentCappedLift hZ d hinj hempty hterminal hn order ha s hs))
        (markedMemoryIndependentHistory hZ d order) := by
  let rename := markedMemoryIndependentUsedPrimeEquiv hZ d hinj hempty
  have hd := congrArg (markedMemoryFiniteTableau_toIndependent hZ)
    (markedMemoryIndependentCappedTableau_recovery hZ d hinj hempty hterminal hn order ha)
  have hh := markedMemoryIndependentHistory_congr_heq hZ hd order
  have hf := markedMemoryFinite_restore_history_heq hZ (markedMemoryIndependentRelabel hZ rename d) order
  have hr := markedMemoryIndependentRelabel_history_heq hZ rename d order
  exact (markedMemoryHistoryTransport_heq hZ _ _).trans (hh.trans (hf.trans hr))

theorem markedMemoryIndependentCappedLift_history
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j)) :
    markedMemoryCappedPathDecoratedAssembly hZ hP s
      (markedMemoryIndependentCappedLift hZ d hinj hempty hterminal hn order ha s hs)=
        markedMemoryHistoryTransport hZ hs (markedMemoryIndependentHistory hZ d order) :=
  eq_of_heq ((markedMemoryIndependentCappedLift_history_heq hZ d hinj hempty hterminal hn order ha s hs hP).trans
    (markedMemoryHistoryTransport_heq hZ hs _).symm)

end
end ArtinMatthews
