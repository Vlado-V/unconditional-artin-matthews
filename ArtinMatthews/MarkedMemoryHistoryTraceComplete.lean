module

public import ArtinMatthews.MarkedMemoryHistoryPresence
public import ArtinMatthews.MarkedMemoryHistoryTrace
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotDeaths
public import ArtinMatthews.MarkedMemoryHistoryGhostDeaths
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

/-! Every actual trace birth is realized; the extension after the terminal
ghost is constant and creates no further particles. -/
namespace ArtinMatthews
noncomputable section

theorem markedMemoryHistoryTraceState_terminal {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) {t : ℕ} (ht : 2*n+1 ≤ t) :
    markedMemoryHistoryTraceState hZ history t = markedMemoryChronologicalTarget hZ history := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => omega
    | succ t => rfl
  | succ n ih =>
    cases t with
    | zero => omega
    | succ t =>
      cases t with
      | zero => omega
      | succ t => exact ih history.2.2 (by omega)

/-- The birth-time tag of every real performed birth lies before the final population. -/
theorem markedMemoryHistoryTraceBirth_time_lt {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (birth : MarkedMemoryHistoryTraceBirth hZ history t) : t < 2*n+1 := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => omega
    | succ t => exact PEmpty.elim birth
  | succ n ih =>
    cases t with
    | zero => omega
    | succ t =>
      cases t with
      | zero => omega
      | succ t => have h := ih history.2.2 t birth; omega

/-- Every actual performed birth has its unique next-population location. -/
theorem markedMemoryHistoryTraceStep_birth_range {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (birth : MarkedMemoryHistoryTraceBirth hZ history t) :
    ∃! i, markedMemoryHistoryTraceStep hZ history t i = Sum.inr birth := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => exact markedMemoryGhostOrigin_birth_range hZ s history birth
    | succ t => exact PEmpty.elim birth
  | succ n ih =>
    cases t with
    | zero => exact markedMemoryGhostOrigin_birth_range hZ s history.1 birth
    | succ t =>
      cases t with
      | zero => exact markedMemoryEdgeSlotOrigin_birth_range hZ _ history.2.1 birth
      | succ t => exact ih history.2.2 t birth

/-- Every actual performed birth is present at its actual birth time. -/
theorem markedMemoryHistoryTraceBirth_present {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (birth : MarkedMemoryHistoryTraceBirth hZ history t) :
    MarkedMemoryLineagePresent
      (T := fun t => MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t))
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) (t+1) (Sum.inr ⟨t,birth⟩) := by
  obtain ⟨i,hi,_⟩ := markedMemoryHistoryTraceStep_birth_range hZ history t birth
  exact ⟨i,by simp only [markedMemoryLineageOrigin, hi, Sum.elim_inr]⟩

end
end ArtinMatthews
