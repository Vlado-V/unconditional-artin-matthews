module

public import ArtinMatthews.MarkedMemoryHistoryChronological
public import ArtinMatthews.MarkedMemoryHistoryBirthIndices
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

/-! Actual performed-birth identities in a chronological history. Identities
are indexed occurrences, not prime values. The separate global distinctness
predicate compares their numeric prime values only after all choices exist.
An empty initial pending memory is a separate boundary requirement. -/
noncomputable section
namespace ArtinMatthews

/-- Ghost batches precede the edge's fresh births, which precede every
later operation. Initial active entries are added separately below. -/
def MarkedMemoryHistoryBirths {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} → MarkedMemoryChronologicalHistory hZ n s → Type _
  | 0,_,ghost => MarkedMemoryGhostBirthIndex ghost
  | _+1,_,history => MarkedMemoryGhostBirthIndex history.1 ⊕
      (MarkedMemoryEdgeBirthIndex history.2.1 ⊕ MarkedMemoryHistoryBirths hZ history.2.2)

def markedMemoryHistoryBirthPrime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → MarkedMemoryHistoryBirths hZ history → Nat.Primes
  | 0,_,ghost => markedMemoryGhostBirthPrime ghost
  | _+1,_,history => Sum.elim (markedMemoryGhostBirthPrime history.1)
      (Sum.elim (markedMemoryEdgeBirthPrime history.2.1) (markedMemoryHistoryBirthPrime hZ history.2.2))

def markedMemoryHistoryHeadGhost {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → MarkedMemoryGhostChoice hZ s
  | 0,_,ghost => ghost
  | _+1,_,history => history.1

def markedMemoryHistoryHeadGhostBirth {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
      MarkedMemoryGhostBirthIndex (markedMemoryHistoryHeadGhost hZ history) ↪ MarkedMemoryHistoryBirths hZ history
  | 0,_,_ => Function.Embedding.refl _
  | _+1,_,_ => Function.Embedding.inl

theorem markedMemoryHistoryHeadGhostBirth_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (birth : MarkedMemoryGhostBirthIndex (markedMemoryHistoryHeadGhost hZ history)) :
    markedMemoryHistoryBirthPrime hZ history (markedMemoryHistoryHeadGhostBirth hZ history birth)=
      markedMemoryGhostBirthPrime (markedMemoryHistoryHeadGhost hZ history) birth := by
  cases n <;> rfl

/-- Exact performed-birth distinctness: initial active entries, actual ghost
births, and actually fresh target entries. Unperformed draws have no address. -/
def MarkedMemoryHistoryBirthDistinct {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) : Prop :=
  Function.Injective (Sum.elim (fun a : Σ _j : J, Fin (pads+1) => (s.2.1 a.1 a.2).1)
    (markedMemoryHistoryBirthPrime hZ history))

theorem markedMemoryHistoryBirthDistinct_initial {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hd : MarkedMemoryHistoryBirthDistinct hZ history) :
    Function.Injective (fun a : Σ _j : J, Fin (pads+1) => (s.2.1 a.1 a.2).1) := by
  intro a b hab
  exact Sum.inl.inj (hd (show Sum.elim _ (markedMemoryHistoryBirthPrime hZ history) (Sum.inl a)=
    Sum.elim _ (markedMemoryHistoryBirthPrime hZ history) (Sum.inl b) from hab))

theorem markedMemoryHistoryBirthDistinct_performed {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hd : MarkedMemoryHistoryBirthDistinct hZ history) :
    Function.Injective (markedMemoryHistoryBirthPrime hZ history) := by
  intro a b hab
  exact Sum.inr.inj (hd (show Sum.elim (fun a : Σ _j : J, Fin (pads+1) => (s.2.1 a.1 a.2).1) _ (Sum.inr a)=
    Sum.elim (fun a : Σ _j : J, Fin (pads+1) => (s.2.1 a.1 a.2).1) _ (Sum.inr b) from hab))

theorem markedMemoryHistoryBirthDistinct_head_ghost {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hd : MarkedMemoryHistoryBirthDistinct hZ history) :
    Function.Injective (markedMemoryGhostBirthPrime (markedMemoryHistoryHeadGhost hZ history)) := by
  intro a b hab
  apply (markedMemoryHistoryHeadGhostBirth hZ history).injective
  apply markedMemoryHistoryBirthDistinct_performed hZ history hd
  simpa only [markedMemoryHistoryHeadGhostBirth_prime] using hab

end ArtinMatthews
