module

public import ArtinMatthews.MarkedMemoryFiniteTableau
public import ArtinMatthews.MarkedMemoryFiniteTableauRestrictionData


set_option backward.privateInPublic true
@[expose] public section

/-! Every actual independent lifespan record restricts to the finite
tableau. The proof uses its local laws directly and stores no record. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)} {n : ℕ}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryFiniteData_laws :
    MarkedMemoryFiniteTableauLaws hZ B (markedMemoryFiniteData_ofIndependent hZ d) where
  lifespan j := {
    nonempty := by
      intro a
      exact (d.lifespan j).nonempty a
    initial_mem := by
      intro a
      simpa only [markedMemoryFiniteData_initial,markedMemoryFiniteData_first,markedMemoryFiniteData_last,
        markedMemoryFiniteData_active hZ d 0 (by omega) j a] using (d.lifespan j).initial_mem a
    ghost_active := by
      intro t ht he a
      simpa only [markedMemoryFiniteData_active hZ d (t+1) (by omega) j a,
        markedMemoryFiniteData_active hZ d t (by omega) j a] using (d.lifespan j).ghost_active t ht he a
    ghost_births := by
      intro t ht he a
      simpa only [markedMemoryFiniteData_births_stage hZ d t ht he j,markedMemoryFiniteData_first,
        markedMemoryFiniteData_last,markedMemoryFiniteData_active hZ d t (by omega) j a] using
        (d.lifespan j).ghost_births t ht he a
    edge_distinct := by
      intro t ht he
      simpa only [markedMemoryFiniteData_incoming_stage hZ d t ht he j,
        markedMemoryFiniteData_outgoing_stage hZ d t ht he j] using (d.lifespan j).edge_distinct t ht he
    edge_outgoing_active := by
      intro t ht he
      simpa only [markedMemoryFiniteData_active hZ d t (by omega) j,
        markedMemoryFiniteData_outgoing_stage hZ d t ht he j] using (d.lifespan j).edge_outgoing_active t ht he
    edge_outgoing_alive := by
      intro t ht he
      simpa only [markedMemoryFiniteData_first,markedMemoryFiniteData_last,
        markedMemoryFiniteData_outgoing_stage hZ d t ht he j] using (d.lifespan j).edge_outgoing_alive t ht he
    edge_active := by
      intro t ht he a
      simpa only [markedMemoryFiniteData_active hZ d t (by omega) j a,
        markedMemoryFiniteData_active hZ d (t+1) (by omega) j a,
        markedMemoryFiniteData_outgoing_stage hZ d t ht he j,
        markedMemoryFiniteData_incoming_stage hZ d t ht he j] using (d.lifespan j).edge_active t ht he a
    edge_births := by
      intro t ht he a
      simpa only [markedMemoryFiniteData_first,markedMemoryFiniteData_incoming_stage hZ d t ht he j] using
        (d.lifespan j).edge_births t ht he a
    edge_deaths := by
      intro t ht he a
      simpa only [markedMemoryFiniteData_last,markedMemoryFiniteData_outgoing_stage hZ d t ht he j] using
        (d.lifespan j).edge_deaths t ht he a }
  active_mem := by
    intro v hv j a
    simpa only [markedMemoryFiniteData_active hZ d (2*v) (by omega) j a,
      markedMemoryFiniteData_activeId hZ d v hv j] using d.active_mem v hv j a
  active_alive := by
    intro v hv j i
    simpa only [markedMemoryFiniteData_first,markedMemoryFiniteData_last,
      markedMemoryFiniteData_activeId hZ d v hv j] using d.active_alive v hv j i
  cutoff := by
    intro t ht
    simpa only [markedMemoryFiniteData_pending hZ d t ht] using d.cutoff t ht
  ghost_death_hit := by
    intro v hv j a
    simpa only [markedMemoryFiniteData_first,markedMemoryFiniteData_last,
      markedMemoryFiniteData_active hZ d (2*v) (by omega) j a,
      markedMemoryFiniteData_position hZ d v hv,markedMemoryFiniteData_particle] using
      d.ghost_death_hit v hv j a
  ghost_birth_anchor := by
    intro v hv j a
    simpa only [markedMemoryFiniteData_births hZ d v hv j,
      markedMemoryFiniteData_position hZ d v hv,markedMemoryFiniteData_particle] using
      d.ghost_birth_anchor v hv j a
  promotion_hit := by
    intro v hv j
    simpa only [markedMemoryFiniteData_first,markedMemoryFiniteData_last,
      markedMemoryFiniteData_incoming hZ d v hv j,
      markedMemoryFiniteData_active hZ d (2*v+1) (by omega) j,
      markedMemoryFiniteData_position hZ d (v+1) (by omega),markedMemoryFiniteData_particle] using
      d.promotion_hit v hv j
  store_anchor := by
    intro v hv j
    simpa only [markedMemoryFiniteData_last,markedMemoryFiniteData_outgoing hZ d v hv j,
      markedMemoryFiniteData_position hZ d v (by omega),markedMemoryFiniteData_particle] using
      d.store_anchor v hv j

def markedMemoryIndependent_toFinite :
    MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n :=
  ⟨markedMemoryFiniteData_ofIndependent hZ d,markedMemoryFiniteData_laws hZ d⟩

end
end ArtinMatthews
