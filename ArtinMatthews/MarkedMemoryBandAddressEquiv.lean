module

public import ArtinMatthews.MarkedMemoryIndependentCorrespondenceGroup
public import ArtinMatthews.MarkedMemoryActualStateReconstruction
public import ArtinMatthews.MarkedMemoryNormalizedAnchors


set_option backward.privateInPublic true
@[expose] public section

/-! Restrict the derived address equivalence to each genuine particle
band. It recovers endpoints, active slots and the complete ordered
pending queues without identifying particles by their numeric primes. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

theorem markedMemorySigmaSubtype_mk {J : Type*} {A : J → Type*} (j : J)
    (x : {a : Sigma A // a.1=j}) :
    (⟨j,Equiv.sigmaSubtype j x⟩ : Sigma A)=x.1 := by
  rcases x with ⟨⟨i,a⟩,h⟩
  cases h
  rfl

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order

def markedMemoryBandAddressEquiv (j : J) : MarkedMemoryActualFiber hZ history j ≃ A j :=
  (Equiv.subtypeEquiv (markedMemoryIndependentAddressEquiv hZ d order)
    (fun a => by rw [markedMemoryIndependentAddress_group hZ d order a])).trans
      (Equiv.sigmaSubtype j)

theorem markedMemoryBandAddressEquiv_sigma (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    (⟨j,markedMemoryBandAddressEquiv hZ d order j a⟩ : Sigma A)=
      markedMemoryIndependentAddressEquiv hZ d order a.1 := by
  unfold markedMemoryBandAddressEquiv
  exact markedMemorySigmaSubtype_mk (A := A) j
    ⟨markedMemoryIndependentAddressEquiv hZ d order a.1,
      (markedMemoryIndependentAddress_group hZ d order a.1).trans a.2⟩

theorem markedMemoryBandAddressEquiv_first (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    markedMemoryActualFirst hZ history j a=
      (d.lifespan j).first (markedMemoryBandAddressEquiv hZ d order j a) := by
  have h := markedMemoryIndependentAddress_birth hZ d order a.1
  rw [← markedMemoryBandAddressEquiv_sigma hZ d order j a] at h
  exact h

theorem markedMemoryBandAddressEquiv_last (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    markedMemoryActualLast hZ history j a=
      (d.lifespan j).last (markedMemoryBandAddressEquiv hZ d order j a) := by
  have h := markedMemoryIndependentAddress_last hZ d order a.1
  rw [← markedMemoryBandAddressEquiv_sigma hZ d order j a] at h
  exact h

theorem markedMemoryBandAddressEquiv_activeId (t : ℕ) (ht : t≤2*n+1) (j : J) (k : Fin (pads+1)) :
    markedMemoryBandAddressEquiv hZ d order j (markedMemoryActualActiveIds hZ history t j k)=
      d.activeId (t/2) j k := by
  have h := (markedMemoryBandAddressEquiv_sigma hZ d order j
    (markedMemoryActualActiveIds hZ history t j k)).trans
      (markedMemoryIndependentAddress_active_slot hZ d order t ht j k)
  exact eq_of_heq (Sigma.mk.inj h).2

theorem markedMemoryBandAddressEquiv_active (t : ℕ) (ht : t≤2*n+1) (j : J)
    (a : MarkedMemoryActualFiber hZ history j) :
    markedMemoryActualActive hZ history t j a ↔
      (d.lifespan j).active t (markedMemoryBandAddressEquiv hZ d order j a) := by
  rw [markedMemoryActualActive,markedMemoryIndependentActive_mem hZ d t ht j]
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨k,(markedMemoryBandAddressEquiv_activeId hZ d order t ht j k).symm⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,(markedMemoryBandAddressEquiv hZ d order j).injective
      ((markedMemoryBandAddressEquiv_activeId hZ d order t ht j k).trans hk)⟩

theorem markedMemoryBandAddressEquiv_queue (t : ℕ) (ht : t≤2*n+1) (j : J) :
    (markedMemoryActualPendingQueue hZ history t j).map (markedMemoryBandAddressEquiv hZ d order j)=
      markedMemoryIndependentQueue hZ d t j := by
  let q := markedMemoryIndependentQueue hZ d t j
  have hl : ((markedMemoryHistoryTraceState hZ history t).2.2.1.1 j:ℕ)=q.length :=
    congrArg (fun z : MarkedRawState P (pads+1) B Z => (z.2.2.1.1 j:ℕ))
      (markedMemoryIndependentHistory_trace_state hZ d order t ht)
  have hk (k : Fin ((markedMemoryHistoryTraceState hZ history t).2.2.1.1 j:ℕ)) :
      markedMemoryBandAddressEquiv hZ d order j (markedMemoryActualPendingIds hZ history t j k)=
        q.get (Fin.cast hl k) := by
    have h := (markedMemoryBandAddressEquiv_sigma hZ d order j
      (markedMemoryActualPendingIds hZ history t j k)).trans
        (markedMemoryIndependentAddress_pending_slot hZ d order t ht j k)
    exact eq_of_heq (Sigma.mk.inj h).2
  rw [markedMemoryActualPendingQueue,List.map_ofFn]
  calc
    _ = List.ofFn (fun k => q.get (Fin.cast hl k)) := congrArg List.ofFn (funext hk)
    _ = List.ofFn q.get := by
      rw [List.ofFn_congr hl]
      congr 1
    _ = q := List.ofFn_get q

theorem markedMemoryBandAddressEquiv_position (v : ℕ) (hv : v≤n) :
    markedMemoryActualPosition hZ history v=d.position v :=
  congrArg Prod.fst (markedMemoryIndependentHistory_trace_even hZ d order v hv)

theorem markedMemoryBandAddressEquiv_prime (j : J) (a : MarkedMemoryActualFiber hZ history j) :
    (markedMemoryActualParticle hZ history j a).1=(d.particle j (markedMemoryBandAddressEquiv hZ d order j a)).1 := by
  apply Subtype.ext
  have h := markedMemoryIndependentAddress_prime hZ d order a.1
  rw [← markedMemoryBandAddressEquiv_sigma hZ d order j a] at h
  exact (markedMemoryActualParticle_prime hZ history j a).trans h.symm

end
end ArtinMatthews
