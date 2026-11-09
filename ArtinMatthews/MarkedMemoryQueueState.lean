module

public import ArtinMatthews.MarkedMemoryIndexedQueues


set_option backward.privateInPublic true
@[expose] public section

/-! Realize bounded ordered particle queues as the literal raw memory
state. No distinctness of numeric primes or particle values is required. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {B : ℕ}

def markedMemoryQueueSizes (queue : (j : J) → List (MarkedRawParticle (P j)))
    (hbound : (∑ j, (queue j).length) ≤ B) : MarkedRawMemorySizes J B :=
  ⟨fun j => ⟨(queue j).length,by
    have h := (Finset.single_le_sum (fun i _ => Nat.zero_le (queue i).length) (Finset.mem_univ j)).trans hbound
    omega⟩,hbound⟩

def markedMemoryQueueState (queue : (j : J) → List (MarkedRawParticle (P j)))
    (hbound : (∑ j, (queue j).length) ≤ B) : MarkedRawMemory P B :=
  ⟨markedMemoryQueueSizes queue hbound,fun j => (queue j).get⟩

theorem markedMemoryQueueState_list (queue : (j : J) → List (MarkedRawParticle (P j)))
    (hbound : (∑ j, (queue j).length) ≤ B) (j : J) :
    List.ofFn ((markedMemoryQueueState queue hbound).2 j) = queue j := List.ofFn_get _

/-- Exact ordered lists determine all bounded raw memory fields, including
the size vector; no quotient by particle values is taken. -/
theorem markedMemoryState_eq_of_lists (a b : MarkedRawMemory P B)
    (hlists : ∀ j, List.ofFn (a.2 j) = List.ofFn (b.2 j)) : a = b := by
  rcases a with ⟨ka,pa⟩
  rcases b with ⟨kb,pb⟩
  have hk : ka = kb := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    have h := congrArg List.length (hlists j)
    simpa only [List.length_ofFn] using h
  cases hk
  have hp : pa = pb := by
    funext j
    exact List.ofFn_injective (hlists j)
  cases hp
  rfl

theorem markedMemoryQueueState_recover (m : MarkedRawMemory P B) :
    markedMemoryQueueState (fun j => List.ofFn (m.2 j))
      (by simpa only [List.length_ofFn] using m.1.2) = m := by
  apply markedMemoryState_eq_of_lists
  intro j
  exact markedMemoryQueueState_list _ _ j

/-- The original raw ghost target is the unique raw memory with these
ordered survivor-then-birth particle lists. -/
theorem markedMemoryGhostTarget_eq_queue (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) :
    markedRawGhostTargetMemory m z hz del l births =
      markedMemoryQueueState
        (fun j => List.ofFn (fun k : Fin (markedRawGhostSurvivors m del j).card =>
            m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k)) ++
          List.ofFn (fun k : Fin (l.1 j : ℕ) => markedRawAnchoredParticle (P j) (births j k) z hz))
        (by simpa only [List.length_append, List.length_ofFn] using l.2) := by
  apply markedMemoryState_eq_of_lists
  intro j
  rw [markedMemoryQueueState_list]
  exact markedMemoryGhostTargetMemory_list m z hz del l births j

end
end ArtinMatthews
