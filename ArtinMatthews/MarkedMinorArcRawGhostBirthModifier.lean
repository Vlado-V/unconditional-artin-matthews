module

public import ArtinMatthews.MarkedMinorArcRawGhostModifier


set_option backward.privateInPublic true
@[expose] public section

/-! A local ordered-batch multiplier is independent of old pending index
names. Reindexing the actual old deletions leaves the birth block fixed,
so the modified ghost preserves the genuine symmetric-memory domain. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawGhostBirthModifiedApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (Φ : (l : J → Fin (B+1)) → ((j : J) → Fin (l j:ℕ) → ↥(P j)) → ℂ)
    (f : MarkedRawState P M B Z → ℂ) : MarkedRawState P M B Z → ℂ :=
  markedRawGhostModifiedApply ν V qStage ρ hZ (fun _ c => Φ c.sizes.1 c.births) f

theorem markedRawGhostBirthModifiedApply_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (Φ : (l : J → Fin (B+1)) → ((j : J) → Fin (l j:ℕ) → ↥(P j)) → ℂ)
    (f : MarkedRawState P M B Z → ℂ) (s : MarkedRawState P M B Z) :
    markedRawGhostBirthModifiedApply ν V qStage ρ hZ Φ f s =
      ∑ del : MarkedRawGhostDeletion s.2.2,
        if MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2) del then
          ∑ l : MarkedRawGhostBirthSizes s.2.2 del, ∑ births : MarkedRawGhostBirthLabels l,
            ((markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l*
              markedRawGhostBirthMass ν l births:ℝ):ℂ)*
                (Φ l.1 births*f (markedRawGhostTargetState hZ s del l births))
        else 0 := by
  classical
  simpa only [markedRawGhostBirthModifiedApply,markedRawGhostModifiedApply,
    markedMemoryGhostChoiceWeight,markedMemoryGhostChoiceTarget] using
    markedMemoryGhostChoice_sum_deletion hZ s (fun del l births =>
      ((markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l*
        markedRawGhostBirthMass ν l births:ℝ):ℂ)*
          (Φ l.1 births*f (markedRawGhostTargetState hZ s del l births)))

theorem markedRawGhostBirthModifiedApply_permute {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (Φ : (l : J → Fin (B+1)) → ((j : J) → Fin (l j:ℕ) → ↥(P j)) → ℂ)
    (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P M) (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j:ℕ))) :
    markedRawGhostBirthModifiedApply ν V qStage ρ hZ Φ f (z,(a,markedRawMemoryPermute m σ)) =
      markedRawGhostBirthModifiedApply ν V qStage ρ hZ Φ f (z,(a,m)) := by
  classical
  rw [markedRawGhostBirthModifiedApply_sum,markedRawGhostBirthModifiedApply_sum]
  rw [← Equiv.sum_comp (markedRawGhostDeletionPermuteEquiv m σ)]
  apply Finset.sum_congr rfl
  intro del _
  change (if MarkedRawGhostDeletionAllowed (markedRawMemoryPermute m σ) z.1 (hZ _ z.2)
      (markedRawGhostDeletionPermute m σ del) then _ else 0) =
    (if MarkedRawGhostDeletionAllowed m z.1 (hZ _ z.2) del then _ else 0)
  rw [markedRawGhostDeletionAllowed_permute]
  by_cases hd : MarkedRawGhostDeletionAllowed m z.1 (hZ _ z.2) del
  · rw [ite_eq_left hd,ite_eq_left hd]
    change (∑ l : MarkedRawGhostBirthSizes (markedRawMemoryPermute m σ)
        (markedRawGhostDeletionPermute m σ del), ∑ births : MarkedRawGhostBirthLabels l,
      ((markedRawGhostSignedCoefficient V qStage ρ (markedRawMemoryPermute m σ) z.1 (hZ _ z.2)
        (markedRawGhostDeletionPermute m σ del) l*markedRawGhostBirthMass ν l births:ℝ):ℂ)*
          (Φ l.1 births*f (markedRawGhostTargetState hZ (z,(a,markedRawMemoryPermute m σ))
            (markedRawGhostDeletionPermute m σ del) l births))) = _
    rw [← Equiv.sum_comp (markedRawGhostBirthSizesPermuteEquiv m σ del)]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro births _
    change MarkedRawGhostBirthLabels l at births
    rw [markedRawGhostSignedCoefficient_permute,markedRawGhostBirthMass_permute,
      markedRawGhostTargetState_symmetric_permute hZ f hf]
    rfl
  · rw [ite_eq_right hd,ite_eq_right hd]

theorem markedRawGhostBirthModifiedApply_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (Φ : (l : J → Fin (B+1)) → ((j : J) → Fin (l j:ℕ) → ↥(P j)) → ℂ)
    (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun m => markedRawGhostBirthModifiedApply ν V qStage ρ hZ Φ f (z,(a,m))) :=
  fun m σ => markedRawGhostBirthModifiedApply_permute ν V qStage ρ hZ Φ f hf z a m σ

end ArtinMatthews
