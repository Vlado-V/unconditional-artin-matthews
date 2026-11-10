module

public import ArtinMatthews.MarkedMemoryHistoryBirths
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

/-! Every actual chronological birth retains its group and band-prime
label. These indexed labels, rather than a quotient by numeric values,
are used to regroup the genuine prime integration factors. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryGhostBirthLabel {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P M B Z}
    (choice : MarkedMemoryGhostChoice hZ s) (b : MarkedMemoryGhostBirthIndex choice) : Σ j, ↥(P j) :=
  ⟨b.1,choice.births b.1 b.2⟩

def markedMemoryEdgeBirthLabel {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (choice : MarkedMemoryEdgeChoice hZ s) (b : MarkedMemoryEdgeBirthIndex choice) : Σ j, ↥(P j) :=
  ⟨b.1,markedRawEdgeTargetLast (markedRawSlotEquiv choice.1 s).2.2
    choice.2.1.promotions choice.2.1.fresh b.1⟩

def markedMemoryHistoryBirthLabel {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → MarkedMemoryHistoryBirths hZ history → Σ j, ↥(P j)
  | 0,_,ghost => markedMemoryGhostBirthLabel ghost
  | _+1,_,history => Sum.elim (markedMemoryGhostBirthLabel history.1)
      (Sum.elim (markedMemoryEdgeBirthLabel history.2.1) (markedMemoryHistoryBirthLabel hZ history.2.2))

/-- The retained band label has the actual previously defined numeric prime. -/
theorem markedMemoryHistoryBirthLabel_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (b : MarkedMemoryHistoryBirths hZ history) :
    (markedMemoryHistoryBirthLabel hZ history b).2.1 = markedMemoryHistoryBirthPrime hZ history b := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rcases b with b | b | b
    · rfl
    · rfl
    · exact ih history.2.2 b

/-- Exactly ghost births carry a creation factor V; fresh edge births do not. -/
def markedMemoryHistoryBirthIsGhost {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → MarkedMemoryHistoryBirths hZ history → Bool
  | 0,_,_ => fun _ => true
  | _+1,_,history => Sum.elim (fun _ => true)
      (Sum.elim (fun _ => false) (markedMemoryHistoryBirthIsGhost hZ history.2.2))

end
end ArtinMatthews
