module

public import ArtinMatthews.MarkedMemoryHistoryInclude


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine finite reindexing from small-window chronological records
to all large-space records whose every vertex lies in the window. The
birth-distinct specialization retains the literal signed boundary term. -/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (hW : ∀ z ∈ W, IsCoprime z.1 z.2)

def markedMemoryHistoryWindowRecordEquiv (n : ℕ) :
    (Σ s : MarkedRawState P (pads+1) B Z, MarkedMemoryChronologicalHistory hZ n s) ≃
      {a : (Σ s : MarkedRawState P (pads+1) B W, MarkedMemoryChronologicalHistory hW n s) //
        MarkedMemoryHistoryVerticesIn hW Z a.2} where
  toFun a := ⟨⟨markedRawStateInclude h a.1, markedMemoryHistoryInclude h hZ hW n a.2⟩,
    markedMemoryHistoryInclude_vertices h hZ hW n a.2⟩
  invFun a :=
    let s := (markedRawStateWindowEquiv h).symm
      ⟨a.1.1, markedMemoryHistoryVerticesIn_source hW a.1.2 a.2⟩
    ⟨s, markedMemoryHistoryRestrict h hZ hW n s a.1.2
      ((markedMemoryHistoryVerticesIn_iff hW a.1.2).mp a.2).2⟩
  left_inv a := by
    rcases a with ⟨s,H⟩
    exact Sigma.ext rfl (heq_of_eq (markedMemoryHistoryRestrict_include h hZ hW n H))
  right_inv a := by
    let s : MarkedRawState P (pads+1) B Z := (markedRawStateWindowEquiv h).symm
      ⟨a.1.1, markedMemoryHistoryVerticesIn_source hW a.1.2 a.2⟩
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq
      (markedMemoryHistoryInclude_restrict h hZ hW n s a.1.2 _))

theorem markedMemoryHistoryWindow_sum [DecidableEq J] (n : ℕ)
    (F : (s : MarkedRawState P (pads+1) B W) →
      MarkedMemoryChronologicalHistory hW n s → ℂ) :
    (∑ s : MarkedRawState P (pads+1) B Z,
      ∑ H : MarkedMemoryChronologicalHistory hZ n s,
        F (markedRawStateInclude h s) (markedMemoryHistoryInclude h hZ hW n H)) =
      ∑ s : MarkedRawState P (pads+1) B W,
        ∑ H : MarkedMemoryChronologicalHistory hW n s,
          if MarkedMemoryHistoryVerticesIn hW Z H then F s H else 0 := by
  classical
  let A := Σ s : MarkedRawState P (pads+1) B W, MarkedMemoryChronologicalHistory hW n s
  let p := fun a : A => MarkedMemoryHistoryVerticesIn hW Z a.2
  have he := (markedMemoryHistoryWindowRecordEquiv h hZ hW (P := P) (pads := pads) (B := B) n).sum_comp
    (fun a : {a : A // p a} => F a.1.1 a.1.2)
  have hs : (∑ a : {a : A // p a}, F a.1.1 a.1.2) =
      ∑ a : A, if p a then F a.1 a.2 else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter p) (by simp) (fun a : A => F a.1 a.2)).symm
  have hall := he.trans hs
  change (∑ a : (Σ s : MarkedRawState P (pads+1) B Z,
      MarkedMemoryChronologicalHistory hZ n s),
      F (markedRawStateInclude h a.1) (markedMemoryHistoryInclude h hZ hW n a.2)) =
    ∑ a : A, if p a then F a.1 a.2 else 0 at hall
  simpa only [A, p, Fintype.sum_sigma] using hall


end
end ArtinMatthews
