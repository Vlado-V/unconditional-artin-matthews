module

public import ArtinMatthews.MarkedMemoryHistoryTrace
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

/-! Exact equivalence between chronological finite performed-birth addresses
and the time-tagged births of the actual transition trace. -/
namespace ArtinMatthews
noncomputable section

def markedMemoryTraceBirthToFinite {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
      (Σ t, MarkedMemoryHistoryTraceBirth hZ history t) → MarkedMemoryHistoryBirths hZ history
  | 0,_,_,⟨0,b⟩ => b
  | 0,_,_,⟨_+1,b⟩ => PEmpty.elim b
  | _+1,_,_,⟨0,b⟩ => Sum.inl b
  | _+1,_,_,⟨1,b⟩ => Sum.inr (Sum.inl b)
  | _+1,_,history,⟨t+2,b⟩ => Sum.inr (Sum.inr (markedMemoryTraceBirthToFinite hZ history.2.2 ⟨t,b⟩))

def markedMemoryFiniteBirthToTrace {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
      MarkedMemoryHistoryBirths hZ history → (Σ t, MarkedMemoryHistoryTraceBirth hZ history t)
  | 0,_,_,b => ⟨0,b⟩
  | _+1,_,_,Sum.inl b => ⟨0,b⟩
  | _+1,_,_,Sum.inr (Sum.inl b) => ⟨1,b⟩
  | _+1,_,history,Sum.inr (Sum.inr b) =>
      let tb := markedMemoryFiniteBirthToTrace hZ history.2.2 b
      ⟨tb.1+2,tb.2⟩

theorem markedMemoryTraceBirth_roundtrip {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (b : Σ t, MarkedMemoryHistoryTraceBirth hZ history t) :
    markedMemoryFiniteBirthToTrace hZ history (markedMemoryTraceBirthToFinite hZ history b) = b := by
  induction n generalizing s with
  | zero =>
    rcases b with ⟨t,b⟩
    cases t with
    | zero => rfl
    | succ t => exact PEmpty.elim b
  | succ n ih =>
    rcases b with ⟨t,b⟩
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t =>
        have h := ih history.2.2 ⟨t,b⟩
        exact congrArg (fun u : Σ t, MarkedMemoryHistoryTraceBirth hZ history.2.2 t =>
          (⟨u.1+2,u.2⟩ : Σ t, MarkedMemoryHistoryTraceBirth hZ history t)) h

theorem markedMemoryFiniteBirth_roundtrip {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (b : MarkedMemoryHistoryBirths hZ history) :
    markedMemoryTraceBirthToFinite hZ history (markedMemoryFiniteBirthToTrace hZ history b) = b := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rcases b with b | b | b
    · rfl
    · rfl
    · have h := ih history.2.2 b
      change Sum.inr (Sum.inr (markedMemoryTraceBirthToFinite hZ history.2.2
        (markedMemoryFiniteBirthToTrace hZ history.2.2 b))) = Sum.inr (Sum.inr b)
      exact congrArg (fun u => Sum.inr (Sum.inr u)) h

def markedMemoryHistoryTraceBirthEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    (Σ t, MarkedMemoryHistoryTraceBirth hZ history t) ≃ MarkedMemoryHistoryBirths hZ history where
  toFun := markedMemoryTraceBirthToFinite hZ history
  invFun := markedMemoryFiniteBirthToTrace hZ history
  left_inv := markedMemoryTraceBirth_roundtrip hZ history
  right_inv := markedMemoryFiniteBirth_roundtrip hZ history

/-- Time tagging changes no actual birth label. -/
theorem markedMemoryHistoryTraceBirthEquiv_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (b : Σ t, MarkedMemoryHistoryTraceBirth hZ history t) :
    markedMemoryHistoryBirthPrime hZ history (markedMemoryHistoryTraceBirthEquiv hZ history b) =
      markedMemoryHistoryTraceBirthPrime hZ history b.1 b.2 := by
  induction n generalizing s with
  | zero =>
    rcases b with ⟨t,b⟩
    cases t with
    | zero => rfl
    | succ t => exact PEmpty.elim b
  | succ n ih =>
    rcases b with ⟨t,b⟩
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t => exact ih history.2.2 ⟨t,b⟩

end
end ArtinMatthews
