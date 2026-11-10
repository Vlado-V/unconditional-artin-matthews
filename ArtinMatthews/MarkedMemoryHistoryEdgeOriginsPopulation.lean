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

/-! Actual active and pending population identities, independent of their possibly repeated primes. -/
namespace ArtinMatthews

/-- Population indices retain both their band and their actual active/pending slot identity. -/
abbrev MarkedMemoryPopulationIndex {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) :=
  (Σ _j : J, Fin M) ⊕ (Σ j : J, Fin (s.2.2.1.1 j : ℕ))

/-- The actual numeric prime attached to a population identity. This map need not be injective. -/
def markedMemoryPopulationPrime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) : MarkedMemoryPopulationIndex s → Nat.Primes :=
  Sum.elim (fun a => (s.2.1 a.1 a.2).1) (fun a => (s.2.2.2 a.1 a.2).1.1)

/-- Reassociate the literal population by band, without changing any index or prime. -/
def markedMemoryPopulationGroupEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) :
    MarkedMemoryPopulationIndex s ≃ Σ j : J, Fin M ⊕ Fin (s.2.2.1.1 j : ℕ) :=
  (Equiv.sigmaSumDistrib (fun _ : J => Fin M) (fun j => Fin (s.2.2.1.1 j : ℕ))).symm

@[simp] theorem markedMemoryPopulationPrime_active {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) (j : J) (i : Fin M) :
    markedMemoryPopulationPrime s (Sum.inl ⟨j, i⟩) = (s.2.1 j i).1 := rfl

@[simp] theorem markedMemoryPopulationPrime_pending {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (s : MarkedRawState P M B Z) (j : J) (i : Fin (s.2.2.1.1 j : ℕ)) :
    markedMemoryPopulationPrime s (Sum.inr ⟨j, i⟩) = (s.2.2.2 j i).1.1 := rfl

end ArtinMatthews
