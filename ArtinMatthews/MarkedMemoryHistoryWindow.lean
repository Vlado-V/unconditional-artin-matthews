module

public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess


set_option backward.privateInPublic true
@[expose] public section

/-! Literal position-window support of a chronological history. The
recursive gate records every edge target; the source position is kept
separately and together they are exactly all chronological vertices. -/

namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)}
  (hW : ∀ z ∈ W, IsCoprime z.1 z.2)

def MarkedMemoryHistoryAfterWindow (Z : Finset (ℤ × ℤ)) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B W} →
      MarkedMemoryChronologicalHistory hW n s → Prop
  | 0, _, _ => True
  | _+1, _, H => H.2.1.2.1.target.1 ∈ Z ∧
      MarkedMemoryHistoryAfterWindow Z H.2.2

def MarkedMemoryHistoryVerticesIn (Z : Finset (ℤ × ℤ)) {n : ℕ}
    {s : MarkedRawState P (pads+1) B W}
    (H : MarkedMemoryChronologicalHistory hW n s) : Prop :=
  ∀ v : Fin (n+1), (markedMemoryHistoryVertexState hW H v).1.1 ∈ Z

theorem markedMemoryHistoryVerticesIn_iff {n : ℕ}
    {s : MarkedRawState P (pads+1) B W}
    (H : MarkedMemoryChronologicalHistory hW n s) :
    MarkedMemoryHistoryVerticesIn hW Z H ↔
      s.1.1 ∈ Z ∧ MarkedMemoryHistoryAfterWindow hW Z H := by
  induction n generalizing s with
  | zero =>
    constructor
    · intro hv
      exact ⟨hv 0, True.intro⟩
    · rintro ⟨hs, _⟩ v
      exact hs
  | succ n ih =>
    constructor
    · intro hv
      have htail : MarkedMemoryHistoryVerticesIn hW Z H.2.2 :=
        fun v => hv v.succ
      obtain ⟨ht, hrest⟩ := (ih H.2.2).mp htail
      exact ⟨hv 0, ht, hrest⟩
    · rintro ⟨hs, ht, hrest⟩ v
      have htail := (ih H.2.2).mpr ⟨ht, hrest⟩
      exact Fin.cases hs (fun w => htail w) v

theorem markedMemoryHistoryVerticesIn_source {n : ℕ}
    {s : MarkedRawState P (pads+1) B W}
    (H : MarkedMemoryChronologicalHistory hW n s)
    (hH : MarkedMemoryHistoryVerticesIn hW Z H) : s.1.1 ∈ Z :=
  (markedMemoryHistoryVerticesIn_iff hW H).mp hH |>.1

theorem markedMemoryHistoryAfterWindow_target {n : ℕ}
    {s : MarkedRawState P (pads+1) B W}
    (H : MarkedMemoryChronologicalHistory hW n s) (hs : s.1.1 ∈ Z)
    (hH : MarkedMemoryHistoryAfterWindow hW Z H) :
    (markedMemoryChronologicalTarget hW H).1.1 ∈ Z := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih H.2.2 hH.1 hH.2

theorem markedMemoryHistoryVerticesIn_target {n : ℕ}
    {s : MarkedRawState P (pads+1) B W}
    (H : MarkedMemoryChronologicalHistory hW n s)
    (hH : MarkedMemoryHistoryVerticesIn hW Z H) :
    (markedMemoryChronologicalTarget hW H).1.1 ∈ Z := by
  obtain ⟨hs, hrest⟩ := (markedMemoryHistoryVerticesIn_iff hW H).mp hH
  exact markedMemoryHistoryAfterWindow_target hW H hs hrest

end
end ArtinMatthews
