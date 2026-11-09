module

public import ArtinMatthews.MarkedMinorArcRawState
public import Mathlib.Analysis.SpecialFunctions.Exp


set_option backward.privateInPublic true
@[expose] public section

/-! The literal PD04 boundary b at the root position and empty memory,
independent of all ordered active tuples. Its norm uses the tilted ν and
the original factorial memory mass, not the physical σ measure. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedRawBoundaryEmptyMemory {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (B : ℕ) : MarkedRawMemory P B :=
  ⟨⟨fun _ => ⟨0, by omega⟩, by simp⟩, fun _ k => Fin.elim0 k⟩

theorem markedRawBoundaryEmptyMemory_mass {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (B : ℕ) (ν : (j : J) → ↥(P j) → ℝ) :
    markedRawMemoryMass ν (markedRawBoundaryEmptyMemory P B) = 1 := by
  simp only [markedRawMemoryMass, markedRawBoundaryEmptyMemory,
    Nat.factorial_zero, Nat.cast_one, div_one]
  apply Finset.prod_eq_one
  intro j _
  apply Finset.prod_eq_one
  intro k _
  exact Fin.elim0 k

def markedRawBoundary {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (z₀ : Z) (s : MarkedRawState P M B Z) : ℂ :=
  if s.1 = z₀ ∧ s.2.2 = markedRawBoundaryEmptyMemory P B then 1 else 0

def markedRawBoundaryEnergy {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (M B : ℕ) {Z : Finset (ℤ × ℤ)} (z₀ : Z) : ℝ :=
  ∑ s : MarkedRawState P M B Z, markedRawStateMass ν s * ‖markedRawBoundary z₀ s‖ ^ 2

theorem markedRawActiveMass_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (M : ℕ) :
    (∑ a : MarkedRawActive P M, markedRawActiveMass ν a) =
      ∏ j, (∑ p : ↥(P j), ν j p) ^ M := by
  classical
  unfold markedRawActiveMass
  rw [← Fintype.prod_sum (fun j (a : Fin M → ↥(P j)) => ∏ k, ν j (a k))]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Fintype.prod_sum (fun (_k : Fin M) (p : ↥(P j)) => ν j p)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Exact PD04 boundary norm, with every ordered active tuple counted and
the genuine empty-memory factorial equal to one. It holds for every total
memory cutoff B and every root position in the actual finite position set. -/
theorem markedRawBoundaryEnergy_eq {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (M B : ℕ) {Z : Finset (ℤ × ℤ)} (z₀ : Z) :
    markedRawBoundaryEnergy ν M B z₀ = ∏ j, (∑ p : ↥(P j), ν j p) ^ M := by
  classical
  have hterm (z : Z) (a : MarkedRawActive P M) (m : MarkedRawMemory P B) :
      markedRawStateMass ν (z,a,m) * ‖markedRawBoundary z₀ (z,a,m)‖ ^ 2 =
        if z = z₀ then (if m = markedRawBoundaryEmptyMemory P B then markedRawActiveMass ν a else 0) else 0 := by
    by_cases hz : z = z₀ <;> by_cases hm : m = markedRawBoundaryEmptyMemory P B
    · subst m
      simp [markedRawBoundary, markedRawStateMass, hz, markedRawBoundaryEmptyMemory_mass]
    · simp [markedRawBoundary, hz, hm]
    · simp [markedRawBoundary, hz]
    · simp [markedRawBoundary, hz]
  unfold markedRawBoundaryEnergy
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, hterm]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact markedRawActiveMass_sum ν M


theorem markedRawBoundaryEnergy_le_exp {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (M B : ℕ) {Z : Finset (ℤ × ℤ)} (z₀ : Z)
    {ε : ℝ} (hs : ∀ j, (∑ p : ↥(P j), ν j p) ≤ 1+ε) :
    markedRawBoundaryEnergy ν M B z₀ ≤ Real.exp (Fintype.card J * (M : ℝ) * ε) := by
  rw [markedRawBoundaryEnergy_eq]
  calc
    _ ≤ ∏ _j : J, (Real.exp ε)^M := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact pow_nonneg (Finset.sum_nonneg (fun p _ => hν j p)) M
      · intro j _
        apply pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => hν j p))
        exact (hs j).trans (by simpa only [add_comm] using Real.add_one_le_exp ε)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      congr 1
      ring

end ArtinMatthews
