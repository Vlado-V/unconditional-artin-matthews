module

public import ArtinMatthews.MarkedMemoryHistoryPotentialAccess
public import ArtinMatthews.MarkedMemoryPrefixMemo


set_option backward.privateInPublic true
@[expose] public section

/-! A local chronological tail keeps the original global address carrier.
The offset relation is proved for the full history and preserved by taking
its literal tail; no relabeling or suffix reconstruction is assumed. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryMemoGhostIndex {N n : ℕ} (j : ℕ) (h : j+n ≤ N) (t : Fin (n+1)) : Fin (N+1) :=
  ⟨j+t.val,by omega⟩

def markedMemoryMemoEdgeIndex {N n : ℕ} (j : ℕ) (h : j+n ≤ N) (t : Fin n) : Fin N :=
  ⟨j+t.val,by omega⟩

theorem markedMemoryMemoGhostIndex_succ {N n j : ℕ} (h : j+(n+1) ≤ N) (t : Fin (n+1)) :
    markedMemoryMemoGhostIndex j h t.succ=
      markedMemoryMemoGhostIndex (j+1) (show (j+1)+n ≤ N by omega) t := by
  apply Fin.ext
  simp only [markedMemoryMemoGhostIndex,Fin.val_succ]
  omega

theorem markedMemoryMemoEdgeIndex_succ {N n j : ℕ} (h : j+(n+1) ≤ N) (t : Fin n) :
    markedMemoryMemoEdgeIndex j h t.succ=
      markedMemoryMemoEdgeIndex (j+1) (show (j+1)+n ≤ N by omega) t := by
  apply Fin.ext
  simp only [markedMemoryMemoEdgeIndex,Fin.val_succ]
  omega

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)

def MarkedMemoryMemoOffsetValues {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (j : ℕ) (h : j+n ≤ N)
    (v : MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes) : Prop :=
  (∀ (t : Fin (n+1)) (i : J) (k : Fin B),
    v (Sum.inr (Sum.inl ⟨markedMemoryMemoGhostIndex j h t,i,k⟩))=
      markedMemoryPotentialGhostValue hZ history t i k) ∧
  (∀ (t : Fin n) (i : J),v (Sum.inr (Sum.inr ⟨markedMemoryMemoEdgeIndex j h t,i⟩))=
      markedMemoryPotentialEdgeValue hZ history t i)

theorem markedMemoryMemoOffsetValues_full {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ N s) :
    MarkedMemoryMemoOffsetValues hZ history 0 (by omega) (markedMemoryPotentialAddressValue hZ history) := by
  constructor
  · intro t i k
    change markedMemoryPotentialGhostValue hZ history (markedMemoryMemoGhostIndex 0 _ t) i k=
      markedMemoryPotentialGhostValue hZ history t i k
    apply congrArg (fun u => markedMemoryPotentialGhostValue hZ history u i k)
    exact Fin.ext (Nat.zero_add _)
  · intro t i
    change markedMemoryPotentialEdgeValue hZ history (markedMemoryMemoEdgeIndex 0 _ t) i=
      markedMemoryPotentialEdgeValue hZ history t i
    apply congrArg (fun u => markedMemoryPotentialEdgeValue hZ history u i)
    exact Fin.ext (Nat.zero_add _)

theorem markedMemoryMemoOffsetValues_tail {n j : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ (n+1) s) (h : j+(n+1) ≤ N)
    (v : MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes)
    (hv : MarkedMemoryMemoOffsetValues hZ history j h v) :
    MarkedMemoryMemoOffsetValues hZ history.2.2 (j+1) (by omega) v := by
  constructor
  · intro t i k
    have hh := hv.1 t.succ i k
    rw [markedMemoryMemoGhostIndex_succ] at hh
    exact hh
  · intro t i
    have hh := hv.2 t.succ i
    rw [markedMemoryMemoEdgeIndex_succ] at hh
    exact hh

end
end ArtinMatthews
