module

public import ArtinMatthews.MarkedMemoryFiniteTableauData


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite summation type. Admissibility consists only of the
local lifespan/incidence/physical laws on the canonical extension. It
contains no history or coverage/reconstruction hypothesis. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}

structure MarkedMemoryFiniteQueueLaws (d : MarkedMemoryFiniteTableauData A P pads Z n)
    (j : J) : Prop where
  nonempty : ∀ a,d.firstAt j a ≤ d.lastAt j a
  initial_mem : ∀ a,a ∈ d.initialAt j ↔ d.firstAt j a ≤ 0 ∧ 0 ≤ d.lastAt j a ∧ ¬d.activeAt 0 j a
  ghost_active : ∀ t,t < 2*n+1 → t%2=0 → ∀ a,d.activeAt (t+1) j a ↔ d.activeAt t j a
  ghost_births : ∀ t,t < 2*n+1 → t%2=0 → ∀ a,
    a ∈ d.birthsAt t j ↔ d.firstAt j a=t+1 ∧ t+1 ≤ d.lastAt j a ∧ ¬d.activeAt t j a
  edge_distinct : ∀ t,t < 2*n+1 → t%2=1 → d.incomingAt t j ≠ d.outgoingAt t j
  edge_outgoing_active : ∀ t,t < 2*n+1 → t%2=1 → d.activeAt t j (d.outgoingAt t j)
  edge_outgoing_alive : ∀ t,t < 2*n+1 → t%2=1 →
    d.firstAt j (d.outgoingAt t j) ≤ t ∧ t ≤ d.lastAt j (d.outgoingAt t j)
  edge_active : ∀ t,t < 2*n+1 → t%2=1 → ∀ a,
    d.activeAt (t+1) j a ↔ (d.activeAt t j a ∧ a ≠ d.outgoingAt t j) ∨ a=d.incomingAt t j
  edge_births : ∀ t,t < 2*n+1 → t%2=1 → ∀ a,d.firstAt j a=t+1 → a=d.incomingAt t j
  edge_deaths : ∀ t,t < 2*n+1 → t%2=1 → ∀ a,d.lastAt j a=t → a=d.outgoingAt t j

def markedMemoryFiniteQueue (d : MarkedMemoryFiniteTableauData A P pads Z n)
    (h : MarkedMemoryFiniteQueueLaws d j) : MarkedMemoryQueueLifespanData (A j) (2*n+1) where
  first := d.firstAt j
  last := d.lastAt j
  active := fun t => d.activeAt t j
  initial := d.initialAt j
  births := fun t => d.birthsAt t j
  incoming := fun t => d.incomingAt t j
  outgoing := fun t => d.outgoingAt t j
  nonempty := h.nonempty
  bounded := fun a => by have hh := (d.last j a).isLt; change (d.last j a).val ≤ 2*n+1; omega
  initial_nodup := markedMemoryFiniteList_nodup _
  initial_mem := h.initial_mem
  ghost_active := h.ghost_active
  ghost_births := h.ghost_births
  ghost_nodup := by
    intro t ht he
    have hv : t/2 ≤ n := by omega
    have hp : t%2=0 ∧ t/2≤n := ⟨he,hv⟩
    simp only [MarkedMemoryFiniteTableauData.birthsAt,dite_eq_left hp]
    exact markedMemoryFiniteList_nodup _
  edge_distinct := h.edge_distinct
  edge_outgoing_active := h.edge_outgoing_active
  edge_outgoing_alive := h.edge_outgoing_alive
  edge_active := h.edge_active
  edge_births := h.edge_births
  edge_deaths := h.edge_deaths

structure MarkedMemoryFiniteTableauLaws (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (B : ℕ) (d : MarkedMemoryFiniteTableauData A P pads Z n) : Prop where
  lifespan : ∀ j,MarkedMemoryFiniteQueueLaws d j
  active_mem : ∀ v,v ≤ n → ∀ j a,d.activeAt (2*v) j a ↔ ∃ i,d.activeIdAt v j i=a
  active_alive : ∀ v,v ≤ n → ∀ j i,
    d.firstAt j (d.activeIdAt v j i) ≤ 2*v ∧ 2*v+1 ≤ d.lastAt j (d.activeIdAt v j i)
  cutoff : ∀ t,t ≤ 2*n+1 → (∑ j,(d.pendingAt t j).card) ≤ B
  ghost_death_hit : ∀ v,v ≤ n → ∀ j a,
    d.firstAt j a ≤ 2*v → d.lastAt j a=2*v → ¬d.activeAt (2*v) j a →
      MarkedRawParticleHits (P j) (d.positionAt v).1 (hZ _ (d.positionAt v).2) (d.particle j a)
  ghost_birth_anchor : ∀ v,v ≤ n → ∀ j a,a ∈ d.birthsAt (2*v) j →
    d.particle j a=markedRawAnchoredParticle (P j) (d.particle j a).1
      (d.positionAt v).1 (hZ _ (d.positionAt v).2)
  promotion_hit : ∀ v,v < n → ∀ j,
    d.firstAt j (d.incomingAt (2*v+1) j) ≤ 2*v+1 →
    2*v+1 ≤ d.lastAt j (d.incomingAt (2*v+1) j) → ¬d.activeAt (2*v+1) j (d.incomingAt (2*v+1) j) →
      MarkedRawParticleHits (P j) (d.positionAt (v+1)).1 (hZ _ (d.positionAt (v+1)).2)
        (d.particle j (d.incomingAt (2*v+1) j))
  store_anchor : ∀ v,v < n → ∀ j,2*v+1 < d.lastAt j (d.outgoingAt (2*v+1) j) →
    d.particle j (d.outgoingAt (2*v+1) j)=
      markedRawAnchoredParticle (P j) (d.particle j (d.outgoingAt (2*v+1) j)).1
        (d.positionAt v).1 (hZ _ (d.positionAt v).2)

def MarkedMemoryFiniteTableau (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (n : ℕ) :=
  {d : MarkedMemoryFiniteTableauData A P pads Z n // MarkedMemoryFiniteTableauLaws hZ B d}

instance markedMemoryFiniteTableau_fintype (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) :
    Fintype (MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n) := by
  classical
  unfold MarkedMemoryFiniteTableau
  infer_instance

def markedMemoryFiniteTableau_toIndependent (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (d : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n) :
    MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n where
  lifespan := fun j => markedMemoryFiniteQueue d.1 (d.2.lifespan j)
  position := d.1.positionAt
  activeId := d.1.activeIdAt
  particle := d.1.particle
  active_mem := d.2.active_mem
  active_alive := d.2.active_alive
  cutoff := d.2.cutoff
  ghost_death_hit := d.2.ghost_death_hit
  ghost_birth_anchor := d.2.ghost_birth_anchor
  promotion_hit := d.2.promotion_hit
  store_anchor := d.2.store_anchor

end
end ArtinMatthews
