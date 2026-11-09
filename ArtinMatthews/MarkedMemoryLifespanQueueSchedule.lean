module

public import ArtinMatthews.MarkedMemoryLifespanQueues


set_option backward.privateInPublic true
@[expose] public section

/-! Construct every pending queue from an independent finite family of
lifespan intervals and active-run incidences. Local ghost/edge incidence
rules suffice; no chronological history or pending-state sequence is given. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A : Type*} [DecidableEq A]

structure MarkedMemoryQueueLifespanData (A : Type*) (H : ℕ) where
  first : A → ℕ
  last : A → ℕ
  active : ℕ → A → Prop
  initial : List A
  births : ℕ → List A
  incoming : ℕ → A
  outgoing : ℕ → A
  nonempty : ∀ a, first a ≤ last a
  bounded : ∀ a, last a ≤ H
  initial_nodup : initial.Nodup
  initial_mem : ∀ a, a ∈ initial ↔ first a ≤ 0 ∧ 0 ≤ last a ∧ ¬ active 0 a
  ghost_active : ∀ t, t < H → t % 2 = 0 → ∀ a, active (t+1) a ↔ active t a
  ghost_births : ∀ t, t < H → t % 2 = 0 → ∀ a,
    a ∈ births t ↔ first a = t+1 ∧ t+1 ≤ last a ∧ ¬ active t a
  ghost_nodup : ∀ t, t < H → t % 2 = 0 → (births t).Nodup
  edge_distinct : ∀ t, t < H → t % 2 = 1 → incoming t ≠ outgoing t
  edge_outgoing_active : ∀ t, t < H → t % 2 = 1 → active t (outgoing t)
  edge_outgoing_alive : ∀ t, t < H → t % 2 = 1 → first (outgoing t) ≤ t ∧ t ≤ last (outgoing t)
  edge_active : ∀ t, t < H → t % 2 = 1 → ∀ a,
    active (t+1) a ↔ (active t a ∧ a ≠ outgoing t) ∨ a = incoming t
  edge_births : ∀ t, t < H → t % 2 = 1 → ∀ a, first a = t+1 → a = incoming t
  edge_deaths : ∀ t, t < H → t % 2 = 1 → ∀ a, last a = t → a = outgoing t

def markedMemoryPendingQueueAt {H : ℕ} (d : MarkedMemoryQueueLifespanData A H) : ℕ → List A
  | 0 => d.initial
  | t+1 => if t % 2 = 0 then
      markedMemoryGhostQueue (markedMemoryPendingQueueAt d t) (d.births t) d.last t
    else markedMemoryEdgeQueue (markedMemoryPendingQueueAt d t) (d.incoming t) (d.outgoing t)
      (decide (t < d.last (d.outgoing t)))

/-- Queue uniqueness and the exact alive-inactive incidence are maintained
through the entire finite independent lifespan schedule. -/
theorem markedMemoryPendingQueueAt_correct {H : ℕ} (d : MarkedMemoryQueueLifespanData A H)
    (t : ℕ) (ht : t ≤ H) :
    (markedMemoryPendingQueueAt d t).Nodup ∧
      ∀ a, a ∈ markedMemoryPendingQueueAt d t ↔ d.first a ≤ t ∧ t ≤ d.last a ∧ ¬ d.active t a := by
  induction t with
  | zero => exact ⟨d.initial_nodup,d.initial_mem⟩
  | succ t ih =>
    have ht' : t < H := by omega
    obtain ⟨hnodup,hmem⟩ := ih (by omega)
    by_cases he : t % 2 = 0
    · simp only [markedMemoryPendingQueueAt, he, ite_true]
      refine ⟨markedMemoryGhostQueue_nodup _ _ d.first d.last t hnodup
        (d.ghost_nodup t ht' he) (fun a ha => ((hmem a).mp ha).1)
        (fun a ha => ((d.ghost_births t ht' he a).mp ha).1),?_⟩
      intro a
      have h := markedMemoryGhostQueue_interval _ _ d.first d.last t (d.active t)
        hmem (d.ghost_births t ht' he) a
      exact h.trans (and_congr_right (fun _ => and_congr_right (fun _ => not_congr (d.ghost_active t ht' he a).symm)))
    · have ho : t % 2 = 1 := by omega
      simp only [markedMemoryPendingQueueAt, he, ite_false]
      refine ⟨markedMemoryEdgeQueue_nodup _ _ _ _ hnodup ?_,?_⟩
      · intro hm
        exact ((hmem (d.outgoing t)).mp hm).2.2 (d.edge_outgoing_active t ht' ho)
      · intro a
        exact markedMemoryEdgeQueue_interval _ _ _ d.first d.last t (d.active t) (d.active (t+1))
          (d.edge_distinct t ht' ho) (d.edge_outgoing_active t ht' ho) (d.edge_outgoing_alive t ht' ho)
          (d.edge_active t ht' ho) (d.edge_births t ht' ho) (d.edge_deaths t ht' ho) hmem a

theorem markedMemoryPendingQueueAt_nodup {H : ℕ} (d : MarkedMemoryQueueLifespanData A H)
    (t : ℕ) (ht : t ≤ H) : (markedMemoryPendingQueueAt d t).Nodup :=
  (markedMemoryPendingQueueAt_correct d t ht).1

theorem markedMemoryPendingQueueAt_mem {H : ℕ} (d : MarkedMemoryQueueLifespanData A H)
    (t : ℕ) (ht : t ≤ H) (a : A) :
    a ∈ markedMemoryPendingQueueAt d t ↔ d.first a ≤ t ∧ t ≤ d.last a ∧ ¬ d.active t a :=
  (markedMemoryPendingQueueAt_correct d t ht).2 a

def markedMemoryPendingIdentitySet [Fintype A] {H : ℕ} (d : MarkedMemoryQueueLifespanData A H)
    (t : ℕ) : Finset A :=
  Finset.univ.filter (fun a => d.first a ≤ t ∧ t ≤ d.last a ∧ ¬ d.active t a)

/-- A cardinal cutoff on the independent pending lifespan set is exactly
a length cutoff on the constructed literal queue. -/
theorem markedMemoryPendingQueueAt_length [Fintype A] {H : ℕ}
    (d : MarkedMemoryQueueLifespanData A H) (t : ℕ) (ht : t ≤ H) :
    (markedMemoryPendingQueueAt d t).length = (markedMemoryPendingIdentitySet d t).card := by
  apply markedMemoryQueue_length_eq_card _ _ (markedMemoryPendingQueueAt_nodup d t ht)
  intro a
  simpa only [markedMemoryPendingIdentitySet, Finset.mem_filter, Finset.mem_univ, true_and] using
    markedMemoryPendingQueueAt_mem d t ht a

theorem markedMemoryPendingQueueAt_bound [Fintype A] {H : ℕ}
    (d : MarkedMemoryQueueLifespanData A H) (t : ℕ) (ht : t ≤ H) (B : ℕ)
    (hB : (markedMemoryPendingIdentitySet d t).card ≤ B) :
    (markedMemoryPendingQueueAt d t).length ≤ B := by
  rwa [markedMemoryPendingQueueAt_length d t ht]

end
end ArtinMatthews
