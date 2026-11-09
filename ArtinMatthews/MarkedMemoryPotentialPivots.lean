module

public import ArtinMatthews.MarkedBirthChronologicalPivots
public import ArtinMatthews.MarkedMemoryPotentialOrderCases


set_option backward.privateInPublic true
@[expose] public section

/-! Exact rank-many earlier-pivot constraints for the actual finite
potential birth carrier. The chosen chronological order is passed
explicitly; the carrier's ordinary equality and rank are unchanged. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J P : Type*} [Fintype J] [DecidableEq J] {M B n : ℕ}

def markedMemoryPotentialNonpivots
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n)) :
    Finset (MarkedMemoryPotentialAddress J M B n) :=
  @markedBirthCycleNonpivots (MarkedMemoryPotentialAddress J M B n) inferInstance inferInstance
    markedMemoryPotentialChronologicalOrder σ

def markedMemoryPotentialPivot
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n)) :
    MarkedMemoryPotentialAddress J M B n → MarkedMemoryPotentialAddress J M B n :=
  @markedBirthChronologicalPivot (MarkedMemoryPotentialAddress J M B n) inferInstance inferInstance
    markedMemoryPotentialChronologicalOrder σ

theorem markedMemoryPotentialNonpivots_card
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n)) :
    (markedMemoryPotentialNonpivots σ).card=markedBirthPermutationRank σ :=
  @markedBirthCycleNonpivots_card (MarkedMemoryPotentialAddress J M B n) inferInstance inferInstance
    markedMemoryPotentialChronologicalOrder σ

theorem markedMemoryPotentialPivot_event
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (p : MarkedMemoryPotentialAddress J M B n → Option P)
    (hσ : MarkedBirthPermutationEvent p σ) {a : MarkedMemoryPotentialAddress J M B n}
    (ha : a∈markedMemoryPotentialNonpivots σ) :
    MarkedMemoryPotentialEarlier (markedMemoryPotentialPivot σ a) a ∧
      markedMemoryPotentialPivot σ a∈σ.support ∧ a∈σ.support ∧
      p a=p (markedMemoryPotentialPivot σ a) ∧ p a≠none :=
  @markedBirthChronologicalPivot_event (MarkedMemoryPotentialAddress J M B n) P inferInstance inferInstance
    markedMemoryPotentialChronologicalOrder σ p hσ a ha

theorem markedMemoryPotentialEvent_iff_pivots
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (p : MarkedMemoryPotentialAddress J M B n → Option P) :
    MarkedBirthPermutationEvent p σ ↔
      (∀ a∈σ.support,p a≠none) ∧
      (∀ a∈markedMemoryPotentialNonpivots σ,p a=p (markedMemoryPotentialPivot σ a)) :=
  @markedBirthPermutationEvent_iff_pivots (MarkedMemoryPotentialAddress J M B n) P inferInstance inferInstance
    markedMemoryPotentialChronologicalOrder σ p

theorem markedMemoryPotentialPivot_time
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (p : MarkedMemoryPotentialAddress J M B n → Option P)
    (hσ : MarkedBirthPermutationEvent p σ) {a : MarkedMemoryPotentialAddress J M B n}
    (ha : a∈markedMemoryPotentialNonpivots σ) :
    markedMemoryPotentialChronologicalTime (markedMemoryPotentialPivot σ a) ≤
      markedMemoryPotentialChronologicalTime a :=
  markedMemoryPotentialEarlier_time (markedMemoryPotentialPivot_event σ p hσ ha).1

variable {PrimeBands : J → Finset Nat.Primes} {pads : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) {s : MarkedRawState PrimeBands (pads+1) B Z}
  (H : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryPotentialHistory_pivot_event
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (hσ : MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ H) σ)
    {a : MarkedMemoryPotentialAddress J (pads+1) B n} (ha : a∈markedMemoryPotentialNonpivots σ) :
    MarkedMemoryPotentialEarlier (markedMemoryPotentialPivot σ a) a ∧
      markedMemoryPotentialPivot σ a∈σ.support ∧ a∈σ.support ∧
      markedMemoryPotentialAddressValue hZ H a=
        markedMemoryPotentialAddressValue hZ H (markedMemoryPotentialPivot σ a) ∧
      markedMemoryPotentialAddressValue hZ H a≠none :=
  markedMemoryPotentialPivot_event σ (markedMemoryPotentialAddressValue hZ H) hσ ha

theorem markedMemoryPotentialHistory_event_iff_pivots
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n)) :
    MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ H) σ ↔
      (∀ a∈σ.support,markedMemoryPotentialAddressValue hZ H a≠none) ∧
      (∀ a∈markedMemoryPotentialNonpivots σ,markedMemoryPotentialAddressValue hZ H a=
        markedMemoryPotentialAddressValue hZ H (markedMemoryPotentialPivot σ a)) :=
  markedMemoryPotentialEvent_iff_pivots σ (markedMemoryPotentialAddressValue hZ H)

end
end ArtinMatthews
