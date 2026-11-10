module

public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsPopulation
public import ArtinMatthews.MarkedMinorArcRawSlotAverage
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual population identities through slot symmetrization. Active slot
indices are permuted; every pending identity remains fixed. -/
namespace ArtinMatthews

def markedMemorySlotPopulationEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) :
    MarkedMemoryPopulationIndex (markedRawSlotEquiv σ s) ≃ MarkedMemoryPopulationIndex s :=
  Equiv.sumCongr (Equiv.sigmaCongrRight (fun j => σ j)) (Equiv.refl _)

@[simp] theorem markedMemorySlotPopulationEquiv_active {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z) (j : J) (i : Fin M) :
    markedMemorySlotPopulationEquiv σ s (Sum.inl ⟨j,i⟩)=Sum.inl ⟨j,σ j i⟩ := rfl

@[simp] theorem markedMemorySlotPopulationEquiv_pending {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z)
    (j : J) (i : Fin (s.2.2.1.1 j : ℕ)) :
    markedMemorySlotPopulationEquiv σ s (Sum.inr ⟨j,i⟩)=Sum.inr ⟨j,i⟩ := rfl

/-- Numeric marks follow their indexed permutation, with repeated values
allowed and no change to pending particle order. -/
theorem markedMemorySlotPopulationEquiv_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (σ : J → Equiv.Perm (Fin M)) (s : MarkedRawState P M B Z)
    (i : MarkedMemoryPopulationIndex (markedRawSlotEquiv σ s)) :
    markedMemoryPopulationPrime s (markedMemorySlotPopulationEquiv σ s i)=
      markedMemoryPopulationPrime (markedRawSlotEquiv σ s) i := by
  rcases i with ⟨j,i⟩ | ⟨j,i⟩ <;> rfl

end ArtinMatthews
