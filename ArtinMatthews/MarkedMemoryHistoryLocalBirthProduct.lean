module

public import ArtinMatthews.MarkedMemoryPotentialBirths
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact product of local birth multipliers along a literal history.
The closed product keeps the chronological ghost and edge visit indices,
including every unperformed potential address. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedMemoryGhostLocalBirthProduct
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    (U : ℕ → J → Fin B → Option Nat.Primes → ℂ) (j : ℕ)
    {s : MarkedRawState P M B Z} (c : MarkedMemoryGhostChoice hZ s) : ℂ :=
  ∏ i, ∏ k : Fin B, U j i k (markedMemoryGhostPotentialValue c i k)

def markedMemoryEdgeLocalBirthProduct
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    (V : ℕ → J → Option Nat.Primes → ℂ) (j : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (c : MarkedMemoryEdgeChoice hZ s) : ℂ :=
  ∏ i, V j i (markedMemoryEdgePotentialValue c i)

def markedMemoryHistoryLocalBirthProduct
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (U : ℕ → J → Fin B → Option Nat.Primes → ℂ) (V : ℕ → J → Option Nat.Primes → ℂ) :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} → MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,j,_,h => markedMemoryGhostLocalBirthProduct U j h
  | n+1,j,_,h => markedMemoryGhostLocalBirthProduct U j h.1 *
      markedMemoryEdgeLocalBirthProduct V j h.2.1 *
      markedMemoryHistoryLocalBirthProduct hZ U V n (j+1) h.2.2

theorem markedMemoryHistoryLocalBirthProduct_eq_visits
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (U : ℕ → J → Fin B → Option Nat.Primes → ℂ) (V : ℕ → J → Option Nat.Primes → ℂ)
    (j : ℕ) {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryLocalBirthProduct hZ U V n j h =
      (∏ t : Fin (n+1), ∏ i, ∏ k : Fin B, U (j+t.1) i k (markedMemoryPotentialGhostValue hZ h t i k)) *
      (∏ t : Fin n, ∏ i, V (j+t.1) i (markedMemoryPotentialEdgeValue hZ h t i)) := by
  induction n generalizing j s with
  | zero =>
    simp only [markedMemoryHistoryLocalBirthProduct,Fin.prod_univ_succ,Fin.prod_univ_zero,
      markedMemoryPotentialGhostValue,markedMemoryGhostLocalBirthProduct,Fin.val_zero,Nat.add_zero,mul_one]
  | succ n ih =>
    rw [markedMemoryHistoryLocalBirthProduct,ih]
    simp only [Fin.prod_univ_succ,markedMemoryPotentialGhostValue,markedMemoryPotentialEdgeValue,
      Fin.cases_zero,Fin.cases_succ,Fin.val_zero,Fin.val_succ,Nat.add_zero,
      markedMemoryGhostLocalBirthProduct,markedMemoryEdgeLocalBirthProduct,Nat.add_assoc,Nat.add_comm 1]
    ring

end ArtinMatthews
