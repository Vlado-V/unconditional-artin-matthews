module

public import ArtinMatthews.MarkedMemoryIndependentPathRecoveryFields
public import ArtinMatthews.MarkedMemoryIndependentRelabel
public import ArtinMatthews.MarkedMemoryFiniteTableauRestriction


set_option backward.privateInPublic true
@[expose] public section

/-! Exact recovery of the whole finite bare endpoint data after the
constructed used-prime relabeling. Ordered birth batches and copied-slot
orders remain genuine separate decorations. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (hinj : Function.Injective (markedMemoryIndependentPrime hZ d))
  (hempty : ∀ j,(d.lifespan j).initial=[])
  (hterminal : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
  (hn : MarkedMemoryBirthNormalized hZ d)
  (order : Fin n → J → Equiv.Perm (Fin pads))
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ d order))

local notation "path" => markedMemoryIndependentActivePath hZ d hinj
local notation "choices" => markedMemoryIndependentPathChoices hZ d
local notation "hc" => markedMemoryIndependentPathChoices_compatible hZ d hinj order hempty hterminal hn ha
local notation "E" => markedMemoryPathEndpointData hZ path choices hc
local notation "rename" => markedMemoryIndependentUsedPrimeEquiv hZ d hinj hempty
local notation "relabeled" => markedMemoryIndependentRelabel hZ rename d

theorem markedMemoryIndependentPathRecovery_endpointData :
    E=markedMemoryEndpointOfData (markedMemoryIndependent_toFinite hZ relabeled).1 := by
  apply MarkedMemoryEndpointData.ext
  · funext j a
    obtain ⟨b,rfl⟩ := (rename j).surjective a
    apply Fin.ext
    change ((E).first j (rename j b)).val=(d.lifespan j).first ((rename j).symm (rename j b))
    rw [Equiv.symm_apply_apply]
    exact markedMemoryIndependentPathRecovery_first hZ d hinj hempty hterminal hn order ha j b
  · funext j a
    obtain ⟨b,rfl⟩ := (rename j).surjective a
    apply Fin.ext
    change ((E).last j (rename j b)).val=(d.lifespan j).last ((rename j).symm (rename j b))
    rw [Equiv.symm_apply_apply]
    exact markedMemoryIndependentPathRecovery_last hZ d hinj hempty hterminal hn order ha j b
  · funext t j
    ext a
    obtain ⟨b,rfl⟩ := (rename j).surjective a
    change (rename j b∈(E).active t j) ↔
      rename j b∈Finset.univ.filter (fun a => (d.lifespan j).active t.val ((rename j).symm a))
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply]
    exact markedMemoryIndependentPathRecovery_active hZ d hinj hempty hterminal hn order ha t j b
  · funext v j
    change (E).incoming v j=rename j ((d.lifespan j).incoming (2*v.val+1))
    exact markedMemoryIndependentPathRecovery_incoming hZ d hinj hempty hterminal hn order ha v j
  · funext v j
    change (E).outgoing v j=rename j ((d.lifespan j).outgoing (2*v.val+1))
    exact markedMemoryIndependentPathRecovery_outgoing hZ d hinj hempty hterminal hn order ha v j
  · funext v
    change (E).position v=d.position v.val
    exact markedMemoryIndependentPathRecovery_position hZ d hinj hempty hterminal hn order ha v
  · funext v j
    apply Function.Embedding.ext
    intro k
    change (E).activeId v j k=rename j (d.activeId v.val j k)
    exact markedMemoryIndependentPathRecovery_activeId hZ d hinj hempty hterminal hn order ha v j k
  · funext j a
    obtain ⟨b,rfl⟩ := (rename j).surjective a
    change (E).particle j (rename j b)=d.particle j ((rename j).symm (rename j b))
    rw [Equiv.symm_apply_apply]
    exact markedMemoryIndependentPathRecovery_particle hZ d hinj hempty hterminal hn order ha j b

end
end ArtinMatthews
