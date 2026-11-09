module

public import ArtinMatthews.MarkedMemoryEndpointData


set_option backward.privateInPublic true
@[expose] public section

/-! The independent tableau laws are unchanged by enumerating the
computed birth identity sets in a different order. The sets themselves
are derived srcBirths endpoint incidence, not supplied as a coverage premise. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryEndpointData A P pads Z n)

local notation "decorate" => markedMemoryEndpointDataDecorated d

theorem markedMemoryEndpointLaws_transfer (srcBirths dstBirths : MarkedMemoryEndpointBirthOrders d)
    (h : MarkedMemoryFiniteTableauLaws hZ B (decorate srcBirths)) :
    MarkedMemoryFiniteTableauLaws hZ B (decorate dstBirths) where
  lifespan j := {
    nonempty := (h.lifespan j).nonempty
    initial_mem := (h.lifespan j).initial_mem
    ghost_active := (h.lifespan j).ghost_active
    ghost_births := by
      intro t ht he a
      exact markedMemoryEndpoint_birthsAt_mem d dstBirths t ht he j a
    edge_distinct := (h.lifespan j).edge_distinct
    edge_outgoing_active := (h.lifespan j).edge_outgoing_active
    edge_outgoing_alive := (h.lifespan j).edge_outgoing_alive
    edge_active := (h.lifespan j).edge_active
    edge_births := (h.lifespan j).edge_births
    edge_deaths := (h.lifespan j).edge_deaths }
  active_mem := h.active_mem
  active_alive := h.active_alive
  cutoff := h.cutoff
  ghost_death_hit := h.ghost_death_hit
  ghost_birth_anchor := by
    intro v hv j a ha
    apply h.ghost_birth_anchor v hv j a
    exact (markedMemoryEndpoint_birthsAt_mem d srcBirths (2*v) (by omega) (by omega) j a).mpr
      ((markedMemoryEndpoint_birthsAt_mem d dstBirths (2*v) (by omega) (by omega) j a).mp ha)
  promotion_hit := h.promotion_hit
  store_anchor := h.store_anchor

theorem markedMemoryEndpointLaws_iff (srcBirths dstBirths : MarkedMemoryEndpointBirthOrders d) :
    MarkedMemoryFiniteTableauLaws hZ B (decorate srcBirths) ↔
      MarkedMemoryFiniteTableauLaws hZ B (decorate dstBirths) :=
  ⟨markedMemoryEndpointLaws_transfer hZ d srcBirths dstBirths,markedMemoryEndpointLaws_transfer hZ d dstBirths srcBirths⟩

def markedMemoryEndpointCanonicalData : MarkedMemoryFiniteTableauData A P pads Z n :=
  decorate (markedMemoryEndpointCanonicalBirths d)

theorem markedMemoryEndpointNormalize_iff (srcBirths dstBirths : MarkedMemoryEndpointBirthOrders d) :
    markedMemoryFiniteAnchorNormalize hZ (decorate srcBirths)=decorate srcBirths ↔
      markedMemoryFiniteAnchorNormalize hZ (decorate dstBirths)=decorate dstBirths := by
  rw [markedMemoryFiniteAnchorNormalize_fixed_iff,markedMemoryFiniteAnchorNormalize_fixed_iff]
  rfl

variable (f : MarkedMemoryFiniteTableau (A := A) (P := P) (pads := pads) (B := B) hZ n)

theorem markedMemoryFiniteTableau_birthSet (v : Fin (n+1)) (j : J) :
    markedMemoryFiniteListSet (f.1.births v j)=markedMemoryEndpointBirthSet (markedMemoryEndpointOfData f.1) v j := by
  ext a
  rw [markedMemoryFiniteListSet_mem]
  have hb := (f.2.lifespan j).ghost_births (2*v.val) (by omega) (by omega) a
  rw [MarkedMemoryFiniteTableauData.birthsAt_valid] at hb
  exact hb.trans (by
    simp only [markedMemoryEndpointBirthSet,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl)

def markedMemoryEndpointOriginalBirths : MarkedMemoryEndpointBirthOrders (markedMemoryEndpointOfData f.1) :=
  fun v j => ⟨f.1.births v j,markedMemoryFiniteTableau_birthSet hZ f v j⟩

theorem markedMemoryEndpointOriginal_rebuild
    (hi : ∀ j,markedMemoryFiniteList_toList (f.1.initial j)=[]) :
    markedMemoryEndpointDataDecorated (markedMemoryEndpointOfData f.1)
      (markedMemoryEndpointOriginalBirths hZ f)=f.1 := by
  apply MarkedMemoryFiniteTableauData.ext <;> try rfl
  funext j
  apply markedMemoryFiniteList_toList_injective
  exact (markedMemoryFiniteList_toList_ofList [] List.nodup_nil).trans (hi j).symm

end
end ArtinMatthews
