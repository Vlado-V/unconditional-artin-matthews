module

public import ArtinMatthews.MarkedBirthDistinctPermutation
public import ArtinMatthews.MarkedMemoryPotentialBirthMap
public import ArtinMatthews.MarkedMemoryPotentialPerformed
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The fixed potential-address predicate is exactly the original
performed-birth distinctness guard. Initial active births are included
with their original indexed multiplicity. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

local instance markedMemoryPotentialAddress_perm_fintype
    {J : Type*} [Fintype J] [DecidableEq J] (M B n : ℕ) :
    Fintype (Equiv.Perm (MarkedMemoryPotentialAddress J M B n)) :=
  @Equiv.instFintype (MarkedMemoryPotentialAddress J M B n)
    (MarkedMemoryPotentialAddress J M B n) inferInstance inferInstance inferInstance inferInstance

abbrev MarkedMemoryAllBirths
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :=
  (Σ _j : J, Fin (pads+1)) ⊕ MarkedMemoryHistoryBirths hZ h

def markedMemoryAllBirthPrime
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryAllBirths hZ h → Nat.Primes :=
  Sum.elim (fun a => (s.2.1 a.1 a.2).1) (markedMemoryHistoryBirthPrime hZ h)

def markedMemoryAllBirthToPotential
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryAllBirths hZ h → MarkedMemoryPotentialAddress J (pads+1) B n :=
  Sum.map (Equiv.sigmaEquivProd J (Fin (pads+1))) (markedMemoryBirthToPotential hZ h)

theorem markedMemoryAllBirthToPotential_injective
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    Function.Injective (markedMemoryAllBirthToPotential hZ h) :=
  Sum.map_injective.mpr ⟨(Equiv.sigmaEquivProd J (Fin (pads+1))).injective,
    markedMemoryBirthToPotential_injective hZ h⟩

theorem markedMemoryAllBirthToPotential_prime
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s)
    (a : MarkedMemoryAllBirths hZ h) :
    markedMemoryPotentialAddressValue hZ h (markedMemoryAllBirthToPotential hZ h a) =
      some (markedMemoryAllBirthPrime hZ h a) := by
  rcases a with a | a
  · rfl
  · exact markedMemoryBirthToPotential_prime hZ h a

theorem markedMemoryAllBirthToPotential_covers
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s)
    (a : MarkedMemoryPotentialAddress J (pads+1) B n)
    (ha : markedMemoryPotentialAddressValue hZ h a ≠ none) :
    ∃ b : MarkedMemoryAllBirths hZ h, markedMemoryAllBirthToPotential hZ h b = a := by
  rcases a with ⟨j,k⟩ | a
  · exact ⟨Sum.inl ⟨j,k⟩,rfl⟩
  · obtain ⟨b,hb⟩ := markedMemoryBirthToPotential_covers hZ h a ha
    exact ⟨Sum.inr b,congrArg Sum.inr hb⟩

theorem markedMemoryHistoryBirthDistinct_iff_potential
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryHistoryBirthDistinct hZ h ↔
      MarkedPerformedInjective (markedMemoryPotentialAddressValue hZ h) := by
  constructor
  · intro hd a ha b hb hab
    obtain ⟨a',rfl⟩ := markedMemoryAllBirthToPotential_covers hZ h a ha
    obtain ⟨b',rfl⟩ := markedMemoryAllBirthToPotential_covers hZ h b hb
    rw [markedMemoryAllBirthToPotential_prime, markedMemoryAllBirthToPotential_prime] at hab
    apply congrArg (markedMemoryAllBirthToPotential hZ h)
    exact hd (Option.some.inj hab)
  · intro hd a b hab
    have ha : markedMemoryPotentialAddressValue hZ h (markedMemoryAllBirthToPotential hZ h a) ≠ none := by
      rw [markedMemoryAllBirthToPotential_prime]
      simp
    have hb : markedMemoryPotentialAddressValue hZ h (markedMemoryAllBirthToPotential hZ h b) ≠ none := by
      rw [markedMemoryAllBirthToPotential_prime]
      simp
    apply markedMemoryAllBirthToPotential_injective hZ h
    apply hd ha hb
    rw [markedMemoryAllBirthToPotential_prime, markedMemoryAllBirthToPotential_prime]
    exact congrArg some hab

theorem markedMemoryHistoryBirthDistinct_permutation_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    (if MarkedMemoryHistoryBirthDistinct hZ h then (1 : ℤ) else 0) =
      ∑ σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n),
        (σ.sign : ℤ) * (if MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ then 1 else 0) := by
  rw [markedMemoryHistoryBirthDistinct_iff_potential]
  exact markedBirthDistinct_permutation_sum _

end ArtinMatthews
