module

public import ArtinMatthews.MarkedMemoryEdgeReconstruction


set_option backward.privateInPublic true
@[expose] public section

/-! Reconstruct an edge from independent lifespan identities. The new
active identity determines an old pending promotion when it matches an
old pending identity; otherwise it has a genuine fresh prime label.
The old active endpoint determines whether that identity is stored. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedMemoryLifespanOldIndex {A : Type*} {k : ℕ} (old : Fin k ↪ A) (target : A) : Option (Fin k) := by
  classical
  exact if h : ∃ i, old i = target then some (Classical.choose h) else none

theorem markedMemoryLifespanOldIndex_eq_some {A : Type*} {k : ℕ}
    (old : Fin k ↪ A) (target : A) (i : Fin k) :
    markedMemoryLifespanOldIndex old target = some i ↔ old i = target := by
  classical
  unfold markedMemoryLifespanOldIndex
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · intro hi
      exact hi ▸ Classical.choose_spec h
    · intro hi
      exact old.injective ((Classical.choose_spec h).trans hi.symm)
  · constructor
    · intro hi
      cases hi
    · intro hi
      exact (h ⟨i,hi⟩).elim

def markedMemoryLifespanLastOrigin {A X : Type*} {k : ℕ}
    (old : Fin k ↪ A) (target : A) (fresh : X) : Fin k ⊕ X :=
  match markedMemoryLifespanOldIndex old target with
  | none => Sum.inr fresh
  | some i => Sum.inl i

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)

structure MarkedMemoryLifespanEdgeData (A : Type*) where
  time : ℕ
  birth : A → ℕ
  last : A → ℕ
  oldPending : (j : J) → Fin (s.2.2.1.1 j : ℕ) ↪ A
  sourceLast : J → A
  targetLast : J → A
  target : Z
  targetPrime : (j : J) → ↥(P j)
  old_present : ∀ j k, birth (oldPending j k) ≤ time ∧ time ≤ last (oldPending j k)
  source_present : ∀ j, birth (sourceLast j) ≤ time ∧ time ≤ last (sourceLast j)
  target_present : ∀ j, birth (targetLast j) ≤ time+1 ∧ time+1 ≤ last (targetLast j)
  fresh_birth : ∀ j, (∀ k, oldPending j k ≠ targetLast j) → birth (targetLast j) = time+1
  old_prime : ∀ j k, oldPending j k = targetLast j → targetPrime j = (s.2.2.2 j k).1
  old_hits : ∀ j k, oldPending j k = targetLast j →
    MarkedRawParticleHits (P j) target.1 (hZ _ target.2) (s.2.2.2 j k)
  memory_bound : (∑ j, ((markedRawGhostSurvivors s.2.2
    (markedRawEdgePromotionDeletion (fun i => markedMemoryLifespanOldIndex (oldPending i) (targetLast i))) j).card +
      (if time < last (sourceLast j) then 1 else 0))) ≤ B

def markedMemoryLifespanEdgeLastOrigin {A : Type*} (d : MarkedMemoryLifespanEdgeData hZ s A) :
    (j : J) → Fin (s.2.2.1.1 j : ℕ) ⊕ ↥(P j) :=
  fun j => markedMemoryLifespanLastOrigin (d.oldPending j) (d.targetLast j) (d.targetPrime j)

theorem markedMemoryLifespanEdgeLastOrigin_promotion {A : Type*} (d : MarkedMemoryLifespanEdgeData hZ s A) :
    markedMemoryRunPromotion s (markedMemoryLifespanEdgeLastOrigin hZ s d) =
      fun j => markedMemoryLifespanOldIndex (d.oldPending j) (d.targetLast j) := by
  funext j
  unfold markedMemoryRunPromotion markedMemoryLifespanEdgeLastOrigin markedMemoryLifespanLastOrigin
  cases markedMemoryLifespanOldIndex (d.oldPending j) (d.targetLast j) <;> rfl

theorem markedMemoryLifespanEdgeLastOrigin_prime {A : Type*} (d : MarkedMemoryLifespanEdgeData hZ s A) :
    markedMemoryRunLastPrime s (markedMemoryLifespanEdgeLastOrigin hZ s d) = d.targetPrime := by
  funext j
  unfold markedMemoryRunLastPrime markedMemoryLifespanEdgeLastOrigin markedMemoryLifespanLastOrigin
  split
  · rfl
  · rename_i k hk
    exact (d.old_prime j k ((markedMemoryLifespanOldIndex_eq_some _ _ _).mp hk)).symm

/-- The old/fresh identity rule and endpoint rule satisfy precisely the
literal edge admissibility checks. -/
def markedMemoryEdgeFromLifespans {A : Type*} (d : MarkedMemoryLifespanEdgeData hZ s A) :
    MarkedMemoryEdgeRunData hZ s where
  target := d.target
  sourceLastSurvives := fun j => decide (d.time < d.last (d.sourceLast j))
  targetLastOrigin := markedMemoryLifespanEdgeLastOrigin hZ s d
  old_hits := by
    intro j k hk
    apply d.old_hits j k
    apply (markedMemoryLifespanOldIndex_eq_some _ _ _).mp
    have hlocal : markedMemoryRunPromotion s (markedMemoryLifespanEdgeLastOrigin hZ s d) j = some k := by
      simp only [markedMemoryRunPromotion, hk, Sum.elim_inl]
    simpa only [markedMemoryLifespanEdgeLastOrigin_promotion] using hlocal
  memory_bound := by
    simpa only [markedMemoryLifespanEdgeLastOrigin_promotion, decide_eq_true_eq] using d.memory_bound

theorem markedMemoryEdgeFromLifespans_promoted_iff {A : Type*} (d : MarkedMemoryLifespanEdgeData hZ s A)
    (j : J) (k : Fin (s.2.2.1.1 j : ℕ)) :
    (markedMemoryEdgeRunReconstruct hZ s (markedMemoryEdgeFromLifespans hZ s d)).promotions j = some k ↔
      d.oldPending j k = d.targetLast j := by
  change markedMemoryRunPromotion s (markedMemoryLifespanEdgeLastOrigin hZ s d) j = some k ↔ _
  rw [markedMemoryLifespanEdgeLastOrigin_promotion, markedMemoryLifespanOldIndex_eq_some]

theorem markedMemoryEdgeFromLifespans_stored_iff {A : Type*} (d : MarkedMemoryLifespanEdgeData hZ s A)
    (j : J) :
    (markedMemoryEdgeRunReconstruct hZ s (markedMemoryEdgeFromLifespans hZ s d)).store j = true ↔
      d.time < d.last (d.sourceLast j) := by
  change decide (d.time < d.last (d.sourceLast j)) = true ↔ _
  exact decide_eq_true_iff

theorem markedMemoryEdgeFromLifespans_target_prime {A : Type*} (d : MarkedMemoryLifespanEdgeData hZ s A) :
    markedRawEdgeTargetLast s.2.2
        (markedMemoryEdgeRunReconstruct hZ s (markedMemoryEdgeFromLifespans hZ s d)).promotions
        (markedMemoryEdgeRunReconstruct hZ s (markedMemoryEdgeFromLifespans hZ s d)).fresh = d.targetPrime := by
  rw [markedMemoryEdgeRunReconstruct_last]
  exact markedMemoryLifespanEdgeLastOrigin_prime hZ s d

end
end ArtinMatthews
