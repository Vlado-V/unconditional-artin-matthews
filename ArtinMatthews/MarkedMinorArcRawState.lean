module

public import ArtinMatthews.MarkedRootProjectiveRootLift
public import Mathlib.Data.Fin.Tuple.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite truncated ordered-state model in PD §4: full active
slots, indexed pending particles with prime and projective anchor, and the
actual factorial memory measure. Repetitions are permitted in this model. -/
namespace ArtinMatthews
open scoped BigOperators LinearAlgebra.Projectivization

instance markedRawPrime_prime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

abbrev MarkedRawPrimeLine (p : Nat.Primes) : Type := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  letI : Field (ZMod (p : ℕ)) := inferInstance
  letI : Module (ZMod (p : ℕ)) (Fin 2 → ZMod (p : ℕ)) := inferInstance
  exact ℙ (ZMod (p : ℕ)) (Fin 2 → ZMod (p : ℕ))

/-- A pending particle includes its actual prime and a counting-measure
projective anchor, as in PD (mem:particle-space). -/
abbrev MarkedRawParticle (P : Finset Nat.Primes) :=
  Σ p : P, MarkedRawPrimeLine p.1

abbrev MarkedRawActive {J : Type*} (P : J → Finset Nat.Primes) (M : ℕ) :=
  (j : J) → Fin M → ↥(P j)

/-- Every group's pending size is explicit, and the total is at most B. -/
abbrev MarkedRawMemorySizes (J : Type*) [Fintype J] (B : ℕ) :=
  {k : J → Fin (B+1) // ∑ j, (k j : ℕ) ≤ B}

/-- Indexed pending lists, allowing repeated prime values and repeated anchors. -/
abbrev MarkedRawMemory {J : Type*} [Fintype J] (P : J → Finset Nat.Primes) (B : ℕ) :=
  Σ k : MarkedRawMemorySizes J B, (j : J) → Fin (k.1 j : ℕ) → MarkedRawParticle (P j)

/-- Actual position, full active ordered lists and total-truncated memory. -/
abbrev MarkedRawState {J : Type*} [Fintype J] (P : J → Finset Nat.Primes)
    (M B : ℕ) (Z : Finset (ℤ × ℤ)) := Z × (MarkedRawActive P M × MarkedRawMemory P B)

/-- The actual product measure of ordered active slots. -/
noncomputable def markedRawActiveMass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) {M : ℕ}
    (a : MarkedRawActive P M) : ℝ := ∏ j, ∏ k, ν j (a j k)

/-- Particle anchor coordinates have counting measure. Only their prime
contributes ν, and every group retains the source divisor k_j!. -/
noncomputable def markedRawMemoryMass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) {B : ℕ}
    (m : MarkedRawMemory P B) : ℝ :=
  ∏ j, (∏ k, ν j (m.2 j k).1)/(Nat.factorial (m.1.1 j : ℕ) : ℝ)

noncomputable def markedRawStateMass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) {M B : ℕ}
    {Z : Finset (ℤ × ℤ)} (s : MarkedRawState P M B Z) : ℝ :=
  markedRawActiveMass ν s.2.1 * markedRawMemoryMass ν s.2.2

/-- Permuting old pending indices preserves every actual particle, its anchor,
and the exact source memory-size vector. -/
def markedRawMemoryPermute {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {B : ℕ}
    (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) : MarkedRawMemory P B :=
  ⟨m.1,fun j k => m.2 j (σ j k)⟩

theorem markedRawMemoryMass_permute {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) {B : ℕ} (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    markedRawMemoryMass ν (markedRawMemoryPermute m σ)=markedRawMemoryMass ν m := by
  unfold markedRawMemoryMass markedRawMemoryPermute
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  exact Equiv.prod_comp (σ j) (fun k => ν j (m.2 j k).1)

/-- Every source measure is nonnegative under the literal prime-atom condition. -/
theorem markedRawStateMass_nonneg {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p, 0 ≤ ν j p) {M B : ℕ}
    {Z : Finset (ℤ × ℤ)} (s : MarkedRawState P M B Z) : 0 ≤ markedRawStateMass ν s := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun j _ => Finset.prod_nonneg (fun k _ => hν j _))
  · exact Finset.prod_nonneg (fun j _ => div_nonneg
      (Finset.prod_nonneg (fun k _ => hν j _)) (Nat.cast_nonneg _))

/-- An indexed particle hits precisely when its actual anchor equals the
projective residue of the actual primitive position. -/
def MarkedRawParticleHits (P : Finset Nat.Primes) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawParticle P) : Prop :=
  a.2=markedPrimePositionLine (a.1.1 : ℕ) z hz

noncomputable def markedRawPendingHits {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) : ℕ := by
  classical
  exact ∑ j, ∑ k, if MarkedRawParticleHits (P j) z hz (m.2 j k) then 1 else 0

/-- Actual pending damping is an endpoint contraction; repeated labels and
anchors remain allowed and are counted by their indices. -/
theorem markedRawPendingDamping_norm_le {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    ‖((ρ^(markedRawPendingHits m z hz) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_of_nonneg (pow_nonneg hρ₀ _)]
  exact pow_le_one₀ hρ₀ hρ₁

/-- Pending-index permutation preserves the actual hit damping, so the clean
operation descends to the source symmetric memory space. -/
theorem markedRawPendingHits_permute {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {B : ℕ} (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ)))
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    markedRawPendingHits (markedRawMemoryPermute m σ) z hz=markedRawPendingHits m z hz := by
  classical
  unfold markedRawPendingHits markedRawMemoryPermute
  apply Finset.sum_congr rfl
  intro j _
  exact Equiv.sum_comp (σ j) (fun k => if MarkedRawParticleHits (P j) z hz (m.2 j k) then 1 else 0)

end ArtinMatthews
