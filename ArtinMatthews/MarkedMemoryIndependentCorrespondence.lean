module

public import ArtinMatthews.MarkedMemoryIndependentTraceStep
public import ArtinMatthews.MarkedMemoryHistoryFiniteLabels


set_option backward.privateInPublic true
@[expose] public section

/-! The reconstructed history has exactly the supplied identity family,
lifespan endpoints and active incidences. The address equivalence is
constructed from actual local transitions and bounded interval support;
it is not part of the independent data. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order

def markedMemoryIndependentFiniteLabels : MarkedMemoryHistoryFiniteLabels hZ history (Σ j, A j) where
  ids := markedMemoryIndependentTraceIds hZ d order
  born := markedMemoryIndependentTraceBirthLabel hZ d order
  first := fun a => (d.lifespan a.1).first a.2
  last := fun a => (d.lifespan a.1).last a.2
  step := markedMemoryIndependentTraceLabel_step hZ d order
  born_first := markedMemoryIndependentTraceBirthLabel_first hZ d order
  life := fun a => (d.lifespan a.1).nonempty a.2
  cap := fun a => (d.lifespan a.1).bounded a.2
  interval := fun a t ht => markedMemoryIndependentTraceIds_interval hZ d order t ht a

def markedMemoryIndependentAddressEquiv : MarkedMemoryHistoryTraceAddress hZ history ≃ Σ j, A j :=
  markedMemoryHistoryFiniteLabelEquiv hZ history (markedMemoryIndependentFiniteLabels hZ d order)

theorem markedMemoryIndependentAddress_birth (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryLineageBirthTime a =
      (d.lifespan (markedMemoryIndependentAddressEquiv hZ d order a).1).first
        (markedMemoryIndependentAddressEquiv hZ d order a).2 :=
  markedMemoryHistoryFiniteLabelEquiv_birth hZ history (markedMemoryIndependentFiniteLabels hZ d order) a

theorem markedMemoryIndependentAddress_last (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryHistoryLifespanLast hZ history a =
      (d.lifespan (markedMemoryIndependentAddressEquiv hZ d order a).1).last
        (markedMemoryIndependentAddressEquiv hZ d order a).2 :=
  markedMemoryHistoryFiniteLabelEquiv_last hZ history (markedMemoryIndependentFiniteLabels hZ d order) a

theorem markedMemoryIndependentAddress_origin (t : ℕ) (ht : t ≤ 2*n+1)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t)) :
    markedMemoryIndependentAddressEquiv hZ d order
      (markedMemoryLineageOrigin (markedMemoryHistoryTraceStep hZ history) t i) =
        markedMemoryIndependentTraceIds hZ d order t ht i :=
  markedMemoryHistoryFiniteLabel_origin hZ history (markedMemoryIndependentFiniteLabels hZ d order) t ht i

theorem markedMemoryIndependentAddress_prime (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryIndependentPrime hZ d (markedMemoryIndependentAddressEquiv hZ d order a) =
      markedMemoryHistoryTraceAddressPrime hZ history a := by
  obtain ⟨t,ht,i,hi⟩ := markedMemoryHistoryTraceAddress_present hZ history a
  have hl : markedMemoryIndependentAddressEquiv hZ d order a = markedMemoryIndependentTraceIds hZ d order t ht i := by
    exact (congrArg (markedMemoryIndependentAddressEquiv hZ d order) hi).symm.trans
      (markedMemoryIndependentAddress_origin hZ d order t ht i)
  rw [hl]
  have hp := markedMemoryHistoryTraceOrigin_prime hZ history t i
  rw [hi] at hp
  exact (markedMemoryIndependentTraceIds_prime hZ d order t ht i).trans hp.symm

theorem markedMemoryIndependentAddress_symm_birth (a : Σ j, A j) :
    markedMemoryLineageBirthTime ((markedMemoryIndependentAddressEquiv hZ d order).symm a) =
      (d.lifespan a.1).first a.2 := by
  exact (markedMemoryIndependentAddress_birth hZ d order ((markedMemoryIndependentAddressEquiv hZ d order).symm a)).trans
    (congrArg (fun x : Σ j, A j => (d.lifespan x.1).first x.2)
      ((markedMemoryIndependentAddressEquiv hZ d order).apply_symm_apply a))

theorem markedMemoryIndependentAddress_symm_last (a : Σ j, A j) :
    markedMemoryHistoryLifespanLast hZ history ((markedMemoryIndependentAddressEquiv hZ d order).symm a) =
      (d.lifespan a.1).last a.2 := by
  exact (markedMemoryIndependentAddress_last hZ d order ((markedMemoryIndependentAddressEquiv hZ d order).symm a)).trans
    (congrArg (fun x : Σ j, A j => (d.lifespan x.1).last x.2)
      ((markedMemoryIndependentAddressEquiv hZ d order).apply_symm_apply a))

theorem markedMemoryIndependentAddress_covers (a : Σ j, A j) :
    ∃ b : MarkedMemoryHistoryTraceAddress hZ history,
      markedMemoryIndependentAddressEquiv hZ d order b = a ∧
        markedMemoryLineageBirthTime b = (d.lifespan a.1).first a.2 ∧
          markedMemoryHistoryLifespanLast hZ history b = (d.lifespan a.1).last a.2 :=
  ⟨(markedMemoryIndependentAddressEquiv hZ d order).symm a, Equiv.apply_symm_apply _ a,
    markedMemoryIndependentAddress_symm_birth hZ d order a, markedMemoryIndependentAddress_symm_last hZ d order a⟩

theorem markedMemoryIndependentAddress_active (a : MarkedMemoryHistoryTraceAddress hZ history)
    (t : ℕ) (ht : t ≤ 2*n+1) :
    (∃ j k, markedMemoryLineageOrigin (markedMemoryHistoryTraceStep hZ history) t (Sum.inl ⟨j,k⟩) = a) ↔
      (d.lifespan (markedMemoryIndependentAddressEquiv hZ d order a).1).active t
        (markedMemoryIndependentAddressEquiv hZ d order a).2 := by
  constructor
  · rintro ⟨j,k,hk⟩
    have hl : markedMemoryIndependentAddressEquiv hZ d order a = ⟨j,d.activeId (t/2) j k⟩ :=
      (congrArg (markedMemoryIndependentAddressEquiv hZ d order) hk).symm.trans
        ((markedMemoryIndependentAddress_origin hZ d order t ht (Sum.inl ⟨j,k⟩)).trans
          (markedMemoryIndependentTraceIds_active hZ d order t ht j k))
    rw [hl]
    exact (markedMemoryIndependentActive_mem hZ d t ht j _).mpr ⟨k,rfl⟩
  · intro ha
    generalize he : markedMemoryIndependentAddressEquiv hZ d order a = b at ha
    rcases b with ⟨j,b⟩
    obtain ⟨k,hk⟩ := (markedMemoryIndependentActive_mem hZ d t ht j b).mp ha
    refine ⟨j,k,(markedMemoryIndependentAddressEquiv hZ d order).injective ?_⟩
    exact (markedMemoryIndependentAddress_origin hZ d order t ht (Sum.inl ⟨j,k⟩)).trans
      ((markedMemoryIndependentTraceIds_active hZ d order t ht j k).trans
        ((congrArg (Sigma.mk j) hk).trans he.symm))

end
end ArtinMatthews
