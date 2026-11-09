module

public import ArtinMatthews.MarkedMinorArcRawGhostState
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.Exponential


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite signed ghost action and its actual ordered birth
integral. Negative deletion and creation coefficients, surviving-hit
q_j/rho² factors, the birth factorials, and total truncation are retained. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The ordered prime birth measure, with the source factorial for each group. -/
noncomputable def markedRawGhostBirthMass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {B : ℕ} {m : MarkedRawMemory P B} {del : MarkedRawGhostDeletion m}
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) : ℝ :=
  ∏ j, (∏ k, ν j (births j k))/(Nat.factorial (l.1 j : ℕ) : ℝ)

/-- Literal signed deletion, surviving-hit and creation coefficients. Here
eta'=1-qStage, as in the actual memory model. No signs are discarded. -/
noncomputable def markedRawGhostSignedCoefficient {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (V : J → ℝ) (qStage ρ : ℝ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) : ℝ :=
  ∏ j, (-(1-qStage)/ρ)^(del j).card*
    (qStage/ρ^2)^((markedRawGroupHitIndices m j z hz \ del j).card)*
    (-(1-qStage)*V j/ρ)^(l.1 j : ℕ)

/-- The literal unrestricted signed ghost row action, with the actual total
memory cutoff. Only hitting old indices may be deleted. Birth prime values
and anchors may repeat, as required before global birth distinctness. -/
noncomputable def markedRawGhostApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ) (s : MarkedRawState P M B Z) : ℂ := by
  classical
  exact ∑ del : MarkedRawGhostDeletion s.2.2,
    if MarkedRawGhostDeletionAllowed s.2.2 s.1.1 (hZ _ s.1.2) del then
      ∑ l : MarkedRawGhostBirthSizes s.2.2 del, ∑ births : MarkedRawGhostBirthLabels l,
        ((markedRawGhostSignedCoefficient V qStage ρ s.2.2 s.1.1 (hZ _ s.1.2) del l*
          markedRawGhostBirthMass ν l births : ℝ) : ℂ)*
          f (markedRawGhostTargetState hZ s del l births)
    else 0

/-- Exact ordered prime-batch integration, with repeated numeric primes
retained as separate indexed choices. Anchors add no factor p+1. -/
theorem markedRawGhost_group_birth_mass {P : Finset Nat.Primes} (ν : P → ℝ) (n : ℕ) :
    (∑ births : Fin n → P, ∏ k, ν (births k))=(∑ p : P, ν p)^n := by
  classical
  have hh := Fintype.prod_sum (fun _ : Fin n => ν)
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh.symm

/-- The literal factorial-weighted birth integral has the exact source mass. -/
theorem markedRawGhostBirthMass_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {B : ℕ} {m : MarkedRawMemory P B} {del : MarkedRawGhostDeletion m}
    (l : MarkedRawGhostBirthSizes m del) :
    (∑ births : MarkedRawGhostBirthLabels l, markedRawGhostBirthMass ν l births)=
      ∏ j, (∑ p : P j, ν j p)^(l.1 j : ℕ)/(Nat.factorial (l.1 j : ℕ) : ℝ) := by
  classical
  unfold markedRawGhostBirthMass
  have hh := Fintype.prod_sum (fun j (birth : Fin (l.1 j : ℕ) → ↥(P j)) =>
    (∏ k, ν j (birth k))/(Nat.factorial (l.1 j : ℕ) : ℝ))
  rw [← hh]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.sum_div,markedRawGhost_group_birth_mass]

theorem markedRawGhostBirthMass_nonneg {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p)
    {B : ℕ} {m : MarkedRawMemory P B} {del : MarkedRawGhostDeletion m}
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) :
    0 ≤ markedRawGhostBirthMass ν l births := by
  exact Finset.prod_nonneg (fun j _ => div_nonneg
    (Finset.prod_nonneg (fun k _ => hν j (births j k))) (Nat.cast_nonneg _))

/-- Every finite ordered birth exponential is bounded by the actual source
exponential, uniformly in its truncation length. -/
theorem markedRawGhost_group_birth_exponential (s c : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c) (B : ℕ) :
    (∑ l ∈ Finset.range (B+1), c^l*s^l/(Nat.factorial l : ℝ)) ≤ Real.exp (c*s) := by
  simpa only [mul_pow] using Real.sum_le_exp_of_nonneg (mul_nonneg hc hs) (B+1)

end ArtinMatthews
