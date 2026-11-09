module

public import ArtinMatthews.MarkedMinorArcRawGhostChargeRule


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite disintegration of the full raw-state pairing into fixed
position and active-slot fibers with the genuine factorial memory measure. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

/-- Position has counting measure; active-slot mass factors out of each
literal memory fiber, without a state-count factor. -/
theorem markedRawStateMass_pairing_fibers {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (f g : MarkedRawState P M B Z → ℂ) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * f s) =
      ∑ z : Z, ∑ a : MarkedRawActive P M, (markedRawActiveMass ν a : ℂ) *
        ∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m : ℂ) * g (z, (a, m)) * f (z, (a, m)) := by
  classical
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [markedRawStateMass, Complex.ofReal_mul]
  ring

/-- Full-state original ghost pairing is exactly its actual memory rule on
fixed position/active fibers. -/
theorem markedRawGhostApply_pairing_fibers {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f g : MarkedRawState P M B Z → ℂ) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawGhostApply ν V qStage ρ hZ f s) =
      ∑ z : Z, ∑ a : MarkedRawActive P M, (markedRawActiveMass ν a : ℂ) *
        ∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m : ℂ) * g (z, (a, m)) *
          markedRawGhostMemoryRule ν (fun _ => -(1-qStage)/ρ) (fun j => -(1-qStage)*V j/ρ)
            (fun _ => qStage/ρ^2) z.1 (hZ _ z.2) (fun m => f (z, (a, m))) m :=
  markedRawStateMass_pairing_fibers ν (markedRawGhostApply ν V qStage ρ hZ f) g

/-- The swapped-charge action has the same exact physical fiber measure. -/
theorem markedRawGhostSwappedApply_pairing_fibers {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f g : MarkedRawState P M B Z → ℂ) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawGhostSwappedApply ν V qStage ρ hZ f s) =
      ∑ z : Z, ∑ a : MarkedRawActive P M, (markedRawActiveMass ν a : ℂ) *
        ∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m : ℂ) * g (z, (a, m)) *
          markedRawGhostMemoryRule ν (fun j => -(1-qStage)*V j/ρ) (fun _ => -(1-qStage)/ρ)
            (fun _ => qStage/ρ^2) z.1 (hZ _ z.2) (fun m => f (z, (a, m))) m :=
  markedRawStateMass_pairing_fibers ν (markedRawGhostSwappedApply ν V qStage ρ hZ f) g

end
end ArtinMatthews
