module

public import ArtinMatthews.MarkedMemoryTransitionAssembly


set_option backward.privateInPublic true
@[expose] public section

/-! Read the literal source-slot permutation at each chronological edge.
The schedule is invariant under a source-state equality transport. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryHistorySourceSlots :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → Fin n → MarkedMemorySlotPermutations J (pads+1)
  | 0, _, _, i => Fin.elim0 i
  | _+1, _, history, i => Fin.cases history.2.1.1
      (fun k => markedMemoryHistorySourceSlots history.2.2 k) i

theorem markedMemoryHistorySourceSlots_transport {n : ℕ} {s t : MarkedRawState P (pads+1) B Z}
    (h : s = t) (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistorySourceSlots hZ (markedMemoryHistoryTransport hZ h history) =
      markedMemoryHistorySourceSlots hZ history := by
  cases h
  rfl

variable {N : ℕ} (d : MarkedMemoryFiniteTransitions (P := P) (pads := pads) (B := B) hZ N)

theorem markedMemoryFiniteTransitions_slots_congr (a b : ℕ) (ha : a < N) (hb : b < N) (h : a = b) :
    (d.edge a ha).1 = (d.edge b hb).1 := by
  subst b
  rfl

theorem markedMemoryFiniteTransitions_segment_slots (remaining start : ℕ) (hb : start+remaining ≤ N)
    (r : Fin remaining) :
    markedMemoryHistorySourceSlots hZ (markedMemoryFiniteTransitions_segment hZ d remaining start hb) r =
      (d.edge (start+r) (by omega)).1 := by
  induction remaining generalizing start with
  | zero => exact Fin.elim0 r
  | succ remaining ih =>
    refine Fin.cases ?_ (fun k => ?_) r
    · rfl
    · change markedMemoryHistorySourceSlots hZ
        (markedMemoryHistoryTransport hZ (d.link start (by omega)).symm
          (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))) k = _
      have hcast := congrFun (markedMemoryHistorySourceSlots_transport hZ (d.link start (by omega)).symm
        (markedMemoryFiniteTransitions_segment hZ d remaining (start+1) (by omega))) k
      have hkval : (k.succ : ℕ) = (k : ℕ)+1 := rfl
      exact hcast.trans ((ih (start+1) (by omega) k).trans
        (markedMemoryFiniteTransitions_slots_congr hZ d ((start+1)+(k : ℕ)) (start+(k.succ : ℕ))
          (by omega) (by omega) (by omega)))

theorem markedMemoryFiniteTransitions_history_slots (r : Fin N) :
    markedMemoryHistorySourceSlots hZ (markedMemoryFiniteTransitions_history hZ d) r = (d.edge r r.2).1 :=
  (markedMemoryFiniteTransitions_segment_slots hZ d N 0 (by omega) r).trans
    (markedMemoryFiniteTransitions_slots_congr hZ d (0+r) r (by omega) r.2 (Nat.zero_add _))

end
end ArtinMatthews
