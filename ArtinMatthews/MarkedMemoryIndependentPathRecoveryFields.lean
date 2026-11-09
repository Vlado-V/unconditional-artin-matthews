module

public import ArtinMatthews.MarkedMemoryIndependentUsedPrimeEquiv
public import ArtinMatthews.MarkedMemoryPathEndpointFields


set_option backward.privateInPublic true
@[expose] public section

/-! Reverse extraction followed by the actual compatible-prime
construction recovers every bare endpoint coordinate. The relabeling
is the derived used-prime equivalence, not a supplied bijection. -/
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
local notation "emb" => markedMemoryIndependentBandPrimeEmbedding hZ d hinj

theorem markedMemoryIndependentPathRecovery_first (j : J) (a : A j) :
    ((E).first j (rename j a)).val=(d.lifespan j).first a := by
  rw [markedMemoryPathEndpoint_first,markedMemoryIndependentUsedPrimeEquiv_prime,
    markedMemoryIndependentPathVisits_at hZ d hinj j a,
    markedMemoryIndependentPathChoices_at hZ d hinj j a]
  exact markedMemoryIndependentIntervalChoice_first hZ d hempty j a

theorem markedMemoryIndependentPathRecovery_last (j : J) (a : A j) :
    ((E).last j (rename j a)).val=(d.lifespan j).last a := by
  rw [markedMemoryPathEndpoint_last,markedMemoryIndependentUsedPrimeEquiv_prime,
    markedMemoryIndependentPathVisits_at hZ d hinj j a,
    markedMemoryIndependentPathChoices_at hZ d hinj j a]
  exact markedMemoryIndependentIntervalChoice_last hZ d hterminal j a

theorem markedMemoryIndependentPathRecovery_active (t : Fin (2*n+2)) (j : J) (a : A j) :
    rename j a∈(E).active t j ↔ (d.lifespan j).active t.val a := by
  rw [markedMemoryPathEndpoint_active,markedMemoryIndependentActive_mem hZ d t.val (by omega)]
  change (∃ k,emb j (d.activeId (t.val/2) j k)=emb j a) ↔ ∃ k,d.activeId (t.val/2) j k=a
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,(emb j).injective hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,congrArg (emb j) hk⟩

theorem markedMemoryIndependentPathRecovery_incoming (v : Fin n) (j : J) :
    (E).incoming v j=rename j ((d.lifespan j).incoming (2*v.val+1)) := by
  apply Subtype.ext
  rfl

theorem markedMemoryIndependentPathRecovery_outgoing (v : Fin n) (j : J) :
    (E).outgoing v j=rename j ((d.lifespan j).outgoing (2*v.val+1)) := by
  apply Subtype.ext
  rfl

theorem markedMemoryIndependentPathRecovery_position (v : Fin (n+1)) :
    (E).position v=d.position v.val := rfl

theorem markedMemoryIndependentPathRecovery_activeId (v : Fin (n+1)) (j : J) (k : Fin (pads+1)) :
    (E).activeId v j k=rename j (d.activeId v.val j k) := by
  apply Subtype.ext
  rfl

theorem markedMemoryIndependentPathRecovery_particle (j : J) (a : A j) :
    (E).particle j (rename j a)=d.particle j a := by
  rw [markedMemoryPathEndpoint_particle]
  have hp : (markedMemoryPrimeBirthVisit
      (markedMemoryPathVisits path j (rename j a).1) (choices j (rename j a).1)).val=
        (d.lifespan j).first a/2 := by
    rw [markedMemoryPrimeBirthVisit_eq_first_div,markedMemoryIndependentUsedPrimeEquiv_prime,
      markedMemoryIndependentPathVisits_at hZ d hinj j a,
      markedMemoryIndependentPathChoices_at hZ d hinj j a,
      markedMemoryIndependentIntervalChoice_first hZ d hempty j a]
  change markedRawAnchoredParticle (P j) (d.particle j a).1 (d.position _).1 _=d.particle j a
  simpa only [hp] using (hn j a).symm

end
end ArtinMatthews
