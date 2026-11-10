module

public import ArtinMatthews.MarkedMinorArcRawState
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Exact tensor-coordinate identification of the actual total-truncated
pending memory. Each group has the literal finite Fock degrees 0,...,B;
the actual source space is precisely the total-degree cutoff inside their
product, with its original factorial product measure. -/
namespace ArtinMatthews
open scoped BigOperators

/-- One actual prime-and-anchor group's finite Fock coordinate. -/
abbrev MarkedRawGroupMemory (P : Finset Nat.Primes) (B : ℕ) :=
  Σ k : Fin (B+1), Fin (k : ℕ) → MarkedRawParticle P

/-- Independent actual group memories before imposing the total cutoff. -/
abbrev MarkedRawAmbientMemory {J : Type*} (P : J → Finset Nat.Primes) (B : ℕ) :=
  (j : J) → MarkedRawGroupMemory (P j) B

def markedRawAmbientMemoryTotal {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {B : ℕ}
    (m : MarkedRawAmbientMemory P B) : ℕ := ∑ j, ((m j).1 : ℕ)

/-- Literal actual memory is exactly the independent-group product with
its true total-degree restriction; no states or repeated indices are lost. -/
def markedRawMemoryAmbientEquiv {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (B : ℕ) :
    MarkedRawMemory P B ≃ {m : MarkedRawAmbientMemory P B // markedRawAmbientMemoryTotal m ≤ B} where
  toFun m := ⟨fun j => ⟨m.1.1 j,m.2 j⟩,m.1.2⟩
  invFun m := ⟨⟨fun j => (m.1 j).1,m.2⟩,fun j => (m.1 j).2⟩
  left_inv m := by rcases m with ⟨⟨k,hk⟩,a⟩; rfl
  right_inv m := by
    apply Subtype.ext
    funext j
    exact Sigma.eta _

/-- Actual tensor-coordinate inclusion, before the total-cutoff projection. -/
def markedRawMemoryToAmbient {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) : MarkedRawAmbientMemory P B :=
  (markedRawMemoryAmbientEquiv P B m).1

theorem markedRawMemoryToAmbient_injective {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} : Function.Injective (markedRawMemoryToAmbient (P := P) (B := B)) :=
  Subtype.val_injective.comp (markedRawMemoryAmbientEquiv P B).injective

/-- The literal group's particle measure has its original factorial. -/
noncomputable def markedRawGroupMemoryMass {P : Finset Nat.Primes}
    (ν : P → ℝ) {B : ℕ} (m : MarkedRawGroupMemory P B) : ℝ :=
  (∏ k, ν (m.2 k).1)/(Nat.factorial (m.1 : ℕ) : ℝ)

noncomputable def markedRawAmbientMemoryMass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {B : ℕ} (m : MarkedRawAmbientMemory P B) : ℝ := ∏ j, markedRawGroupMemoryMass (ν j) (m j)

/-- The exact tensor identification preserves the actual source measure. -/
theorem markedRawMemoryToAmbient_mass {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {B : ℕ} (m : MarkedRawMemory P B) :
    markedRawAmbientMemoryMass ν (markedRawMemoryToAmbient m)=markedRawMemoryMass ν m := rfl

/-- Simultaneous index permutations act only inside the genuine group degree. -/
def markedRawAmbientMemoryPermute {J : Type*}
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawAmbientMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin ((m j).1 : ℕ))) : MarkedRawAmbientMemory P B :=
  fun j => ⟨(m j).1,fun k => (m j).2 (σ j k)⟩

/-- The actual pending-index symmetry is exactly the tensor-coordinate
symmetry; it is not silently imposed on arbitrary ordered functions. -/
theorem markedRawMemoryToAmbient_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    markedRawMemoryToAmbient (markedRawMemoryPermute m σ)=
      markedRawAmbientMemoryPermute (markedRawMemoryToAmbient m) σ := rfl

/-- Complete literal symmetric-pending condition on the source memory. -/
def MarkedRawMemorySymmetric {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (f : MarkedRawMemory P B → ℂ) : Prop :=
  ∀ (m : MarkedRawMemory P B) (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))),
    f (markedRawMemoryPermute m σ)=f m

/-- The source factorial-weighted energy is exactly the tensor energy
restricted by its actual total cutoff, with no degree or group-count loss. -/
theorem markedRawMemory_energy_ambient {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (B : ℕ) (f : MarkedRawMemory P B → ℂ) :
    (∑ m : MarkedRawMemory P B, markedRawMemoryMass ν m*‖f m‖^2)=
      ∑ m : {m : MarkedRawAmbientMemory P B // markedRawAmbientMemoryTotal m ≤ B},
        markedRawAmbientMemoryMass ν m.1*‖f ((markedRawMemoryAmbientEquiv P B).symm m)‖^2 := by
  classical
  have hh := Equiv.sum_comp (markedRawMemoryAmbientEquiv P B).symm
    (fun m => markedRawMemoryMass ν m*‖f m‖^2)
  symm
  calc
    _ = ∑ m : {m : MarkedRawAmbientMemory P B // markedRawAmbientMemoryTotal m ≤ B},
        markedRawMemoryMass ν ((markedRawMemoryAmbientEquiv P B).symm m)*
          ‖f ((markedRawMemoryAmbientEquiv P B).symm m)‖^2 := by
      apply Finset.sum_congr rfl
      intro m _
      rfl
    _ = _ := hh

end ArtinMatthews
