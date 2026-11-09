module

public import ArtinMatthews.MarkedMemoryLifespanQueueSchedule


set_option backward.privateInPublic true
@[expose] public section

/-! Relabel independent lifespan identities by a genuine equivalence.
The full ordered initial and birth lists are mapped, and the reconstructed
queue at every time is their literal image. No finiteness is required for
the queue construction or its naturality. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} (e : A ≃ B)

theorem markedMemoryRelabel_mem_map (l : List A) (b : B) :
    b ∈ l.map e ↔ e.symm b ∈ l := by
  constructor
  · intro hb
    obtain ⟨a,ha,h⟩ := List.mem_map.mp hb
    have he : a = e.symm b := e.eq_symm_apply.mpr h
    simpa only [← he] using ha
  · intro hb
    exact List.mem_map.mpr ⟨e.symm b,hb,e.apply_symm_apply b⟩

def markedMemoryQueueRelabel {H : ℕ} (d : MarkedMemoryQueueLifespanData A H) :
    MarkedMemoryQueueLifespanData B H where
  first b := d.first (e.symm b)
  last b := d.last (e.symm b)
  active t b := d.active t (e.symm b)
  initial := d.initial.map e
  births t := (d.births t).map e
  incoming t := e (d.incoming t)
  outgoing t := e (d.outgoing t)
  nonempty b := d.nonempty (e.symm b)
  bounded b := d.bounded (e.symm b)
  initial_nodup := d.initial_nodup.map e.injective
  initial_mem b := (markedMemoryRelabel_mem_map e d.initial b).trans (d.initial_mem (e.symm b))
  ghost_active t ht he b := d.ghost_active t ht he (e.symm b)
  ghost_births t ht he b := (markedMemoryRelabel_mem_map e (d.births t) b).trans (d.ghost_births t ht he (e.symm b))
  ghost_nodup t ht he := (d.ghost_nodup t ht he).map e.injective
  edge_distinct t ht ho := fun h => d.edge_distinct t ht ho (e.injective h)
  edge_outgoing_active t ht ho := by simpa only [Equiv.symm_apply_apply] using d.edge_outgoing_active t ht ho
  edge_outgoing_alive t ht ho := by simpa only [Equiv.symm_apply_apply] using d.edge_outgoing_alive t ht ho
  edge_active t ht ho b := by
    simpa only [ne_eq, Equiv.symm_apply_eq] using d.edge_active t ht ho (e.symm b)
  edge_births t ht ho b hb := e.symm_apply_eq.mp (d.edge_births t ht ho (e.symm b) hb)
  edge_deaths t ht ho b hb := e.symm_apply_eq.mp (d.edge_deaths t ht ho (e.symm b) hb)

variable [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] [DecidableEq B] in
theorem markedMemoryGhostQueue_relabel (queue born : List A) (last : A → ℕ) (t : ℕ) :
    markedMemoryGhostQueue (queue.map e) (born.map e) (fun b => last (e.symm b)) t =
      (markedMemoryGhostQueue queue born last t).map e := by
  unfold markedMemoryGhostQueue
  rw [List.map_append, List.filter_map]
  simp only [Function.comp_def, Equiv.symm_apply_apply]

theorem markedMemoryEdgeQueue_relabel (queue : List A) (incoming outgoing : A) (store : Bool) :
    markedMemoryEdgeQueue (queue.map e) (e incoming) (e outgoing) store =
      (markedMemoryEdgeQueue queue incoming outgoing store).map e := by
  unfold markedMemoryEdgeQueue
  rw [List.map_append, List.filter_map]
  simp only [Function.comp_def, ne_eq, e.injective.eq_iff]
  cases store <;> rfl

theorem markedMemoryQueueRelabel_queue {H : ℕ} (d : MarkedMemoryQueueLifespanData A H) (t : ℕ) :
    markedMemoryPendingQueueAt (markedMemoryQueueRelabel e d) t =
      (markedMemoryPendingQueueAt d t).map e := by
  induction t with
  | zero => rfl
  | succ t ih =>
    unfold markedMemoryPendingQueueAt
    split_ifs with ht
    · rw [ih]
      exact markedMemoryGhostQueue_relabel e _ _ _ t
    · rw [ih]
      change markedMemoryEdgeQueue ((markedMemoryPendingQueueAt d t).map e)
        (e (d.incoming t)) (e (d.outgoing t))
        (decide (t < d.last (e.symm (e (d.outgoing t))))) = _
      rw [e.symm_apply_apply]
      exact markedMemoryEdgeQueue_relabel e _ _ _ _

theorem markedMemoryQueueRelabel_queue_length {H : ℕ} (d : MarkedMemoryQueueLifespanData A H) (t : ℕ) :
    (markedMemoryPendingQueueAt (markedMemoryQueueRelabel e d) t).length =
      (markedMemoryPendingQueueAt d t).length := by
  rw [markedMemoryQueueRelabel_queue, List.length_map]

omit [DecidableEq A] in
theorem markedMemoryQueueLifespanData_ext {H : ℕ} (d f : MarkedMemoryQueueLifespanData A H)
    (hf : d.first = f.first) (hl : d.last = f.last) (ha : d.active = f.active)
    (hi : d.initial = f.initial) (hb : d.births = f.births)
    (hin : d.incoming = f.incoming) (hout : d.outgoing = f.outgoing) : d = f := by
  cases d
  cases f
  cases hf
  cases hl
  cases ha
  cases hi
  cases hb
  cases hin
  cases hout
  rfl

omit [DecidableEq A] [DecidableEq B] in
theorem markedMemoryQueueRelabel_symm {H : ℕ} (d : MarkedMemoryQueueLifespanData A H) :
    markedMemoryQueueRelabel e.symm (markedMemoryQueueRelabel e d) = d := by
  apply markedMemoryQueueLifespanData_ext
  · funext a; simp only [markedMemoryQueueRelabel, Equiv.symm_symm, Equiv.symm_apply_apply]
  · funext a; simp only [markedMemoryQueueRelabel, Equiv.symm_symm, Equiv.symm_apply_apply]
  · funext t a; simp only [markedMemoryQueueRelabel, Equiv.symm_symm, Equiv.symm_apply_apply]
  · simp only [markedMemoryQueueRelabel, List.map_map, Function.comp_def, Equiv.symm_apply_apply, List.map_id_fun', id_eq]
  · funext t
    simp only [markedMemoryQueueRelabel, List.map_map, Function.comp_def, Equiv.symm_apply_apply, List.map_id_fun', id_eq]
  · funext t; simp only [markedMemoryQueueRelabel, Equiv.symm_apply_apply]
  · funext t; simp only [markedMemoryQueueRelabel, Equiv.symm_apply_apply]

def markedMemoryQueueRelabelEquiv (H : ℕ) :
    MarkedMemoryQueueLifespanData A H ≃ MarkedMemoryQueueLifespanData B H where
  toFun := markedMemoryQueueRelabel e
  invFun := markedMemoryQueueRelabel e.symm
  left_inv := markedMemoryQueueRelabel_symm e
  right_inv d := by simpa only [Equiv.symm_symm] using markedMemoryQueueRelabel_symm e.symm d

theorem markedMemoryQueueRelabel_pending_card [Fintype A] [Fintype B] {H : ℕ}
    (d : MarkedMemoryQueueLifespanData A H) (t : ℕ) (ht : t ≤ H) :
    (markedMemoryPendingIdentitySet (markedMemoryQueueRelabel e d) t).card =
      (markedMemoryPendingIdentitySet d t).card := by
  rw [← markedMemoryPendingQueueAt_length _ t ht, ← markedMemoryPendingQueueAt_length _ t ht,
    markedMemoryQueueRelabel_queue_length]

end
end ArtinMatthews
