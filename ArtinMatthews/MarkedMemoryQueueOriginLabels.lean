module

public import ArtinMatthews.MarkedMemoryQueueOrder
public import ArtinMatthews.MarkedMemoryHistoryOrigins


set_option backward.privateInPublic true
@[expose] public section

/-! Ordered identity labels through the exact survivor/birth index
equivalence. These statements concern identity lists, not numeric prime
values, and supply the local relabeling step of reverse reconstruction. -/
namespace ArtinMatthews
noncomputable section

theorem markedMemoryListGet_ofFn_eq {A : Type*} {k : ℕ} (f : Fin k → A) (queue : List A)
    (h : List.ofFn f = queue) (i : Fin queue.length) :
    queue.get i = f (Fin.cast (by rw [← h, List.length_ofFn]) i) := by
  subst queue
  exact List.get_ofFn f i

def markedMemoryQueueIndexOrigin {A : Type*} (queue : List A) (keep : Finset (Fin queue.length)) (b : ℕ) :
    Fin (keep.card+b) ≃ (keep ⊕ Fin b) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (keep.orderIsoOfFin rfl).toEquiv (Equiv.refl _))

def markedMemoryRetainedAppendTuple {A : Type*} (queue born : List A) (keep : Finset (Fin queue.length)) :
    Fin (keep.card + born.length) → A :=
  Fin.append (fun i => queue.get ((keep.orderIsoOfFin rfl i).1)) born.get

theorem markedMemoryRetainedAppendTuple_list {A : Type*} (queue born : List A) (keep : Finset (Fin queue.length)) :
    List.ofFn (markedMemoryRetainedAppendTuple queue born keep) = markedMemoryRetainedQueue queue keep ++ born := by
  rw [markedMemoryRetainedAppendTuple, List.ofFn_fin_append, List.ofFn_get]
  rfl

theorem markedMemoryRetainedAppendTuple_origin {A : Type*} (queue born : List A) (keep : Finset (Fin queue.length))
    (i : Fin (keep.card + born.length)) :
    Sum.elim (fun old : keep => queue.get old.1) born.get (markedMemoryQueueIndexOrigin queue keep born.length i) =
      markedMemoryRetainedAppendTuple queue born keep i := by
  obtain ⟨x,rfl⟩ := finSumFinEquiv.surjective i
  cases x with
  | inl k => simp [markedMemoryQueueIndexOrigin, markedMemoryRetainedAppendTuple]
  | inr k => simp [markedMemoryQueueIndexOrigin, markedMemoryRetainedAppendTuple]

theorem markedMemoryRetainedAppend_get_origin {A : Type*} (queue born : List A) (keep : Finset (Fin queue.length))
    (i : Fin (markedMemoryRetainedQueue queue keep ++ born).length) :
    (markedMemoryRetainedQueue queue keep ++ born).get i =
      Sum.elim (fun old : keep => queue.get old.1) born.get
        (markedMemoryQueueIndexOrigin queue keep born.length
          (Fin.cast (by simp only [List.length_append, markedMemoryRetainedQueue_length]) i)) := by
  calc
    _ = markedMemoryRetainedAppendTuple queue born keep
        (Fin.cast (by simp only [List.length_append, markedMemoryRetainedQueue_length]) i) :=
      markedMemoryListGet_ofFn_eq _ _ (markedMemoryRetainedAppendTuple_list queue born keep) i
    _ = _ := (markedMemoryRetainedAppendTuple_origin queue born keep _).symm

end
end ArtinMatthews
