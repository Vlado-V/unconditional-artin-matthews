module

public import ArtinMatthews.MarkedMemoryHistoryAnchorGates
public import ArtinMatthews.MarkedMemoryHistoryActualPresence
public import ArtinMatthews.MarkedMemoryHistoryPresenceMarks
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

/-! Prime-and-anchor marks propagate through the genuine chronological
trace. This yields fixed-anchor coherence for every actual indexed active
visit; no coherence condition is postulated. -/
namespace ArtinMatthews
noncomputable section

 def markedMemoryHistoryTraceBirthAnchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → (t : ℕ) →
      MarkedMemoryHistoryTraceBirth hZ history t → MarkedMemoryAnchoredPrime
  | 0, _, ghost, 0 => markedMemoryGhostBirthAnchor ghost
  | 0, _, _, _+1 => PEmpty.elim
  | _+1, _, history, 0 => markedMemoryGhostBirthAnchor history.1
  | _+1, _, history, 1 => markedMemoryEdgeBirthAnchor history.2.1
  | _+1, _, history, t+2 => markedMemoryHistoryTraceBirthAnchor hZ history.2.2 t

 theorem markedMemoryPopulationAnchor_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (i : MarkedMemoryPopulationIndex s) :
    (markedMemoryPopulationAnchor hZ s i).1 = markedMemoryPopulationPrime s i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩ <;> rfl

 theorem markedMemoryHistoryTraceBirthAnchor_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (b : MarkedMemoryHistoryTraceBirth hZ history t) :
    (markedMemoryHistoryTraceBirthAnchor hZ history t b).1 =
      markedMemoryHistoryTraceBirthPrime hZ history t b := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => rfl
    | succ t => exact PEmpty.elim b
  | succ n ih =>
    cases t with
    | zero => rfl
    | succ t =>
      cases t with
      | zero => rfl
      | succ t => exact ih history.2.2 t b

 theorem markedMemoryHistoryTraceStep_anchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (t : ℕ)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history (t+1))) :
    Sum.elim (markedMemoryPopulationAnchor hZ (markedMemoryHistoryTraceState hZ history t))
      (markedMemoryHistoryTraceBirthAnchor hZ history t) (markedMemoryHistoryTraceStep hZ history t i) =
      markedMemoryPopulationAnchor hZ (markedMemoryHistoryTraceState hZ history (t+1)) i := by
  induction n generalizing s t with
  | zero =>
    cases t with
    | zero => exact markedMemoryGhostPopulationOrigin_anchor hZ s history i
    | succ t => rfl
  | succ n ih =>
    cases t with
    | zero => exact markedMemoryGhostPopulationOrigin_anchor hZ s history.1 i
    | succ t =>
      cases t with
      | zero => exact markedMemoryEdgeSlotPopulationOrigin_anchor hZ _ history.2.1 ha.1 i
      | succ t => exact ih history.2.2 ha.2 t i

 def markedMemoryHistoryTraceAddressAnchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryHistoryTraceAddress hZ history → MarkedMemoryAnchoredPrime :=
  Sum.elim (markedMemoryPopulationAnchor hZ s)
    (fun b => markedMemoryHistoryTraceBirthAnchor hZ history b.1 b.2)

 theorem markedMemoryHistoryTraceAddressAnchor_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (a : MarkedMemoryHistoryTraceAddress hZ history) :
    (markedMemoryHistoryTraceAddressAnchor hZ history a).1 =
      markedMemoryHistoryTraceAddressPrime hZ history a := by
  cases a with
  | inl old => exact markedMemoryPopulationAnchor_prime hZ s old
  | inr birth => exact markedMemoryHistoryTraceBirthAnchor_prime hZ history birth.1 birth.2

 theorem markedMemoryHistoryTraceOrigin_anchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (t : ℕ)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t)) :
    markedMemoryHistoryTraceAddressAnchor hZ history
      (markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
        (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t i) =
      markedMemoryPopulationAnchor hZ (markedMemoryHistoryTraceState hZ history t) i :=
  markedMemoryLineageOrigin_mark (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
    (fun t => markedMemoryPopulationAnchor hZ (markedMemoryHistoryTraceState hZ history t))
    (markedMemoryHistoryTraceBirthAnchor hZ history) (markedMemoryHistoryTraceStep_anchor hZ history ha) t i

/-- Every actual active visit to a fixed indexed identity has its unique
birth's (or initial entry's) unchanged projective anchor. -/
 theorem markedMemoryHistoryTrace_active_anchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (a : MarkedMemoryHistoryTraceAddress hZ history) (t : ℕ) (j : J) (k : Fin (pads+1))
    (hi : markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
        t (Sum.inl ⟨j,k⟩) = a) :
    (⟨((markedMemoryHistoryTraceState hZ history t).2.1 j k).1,
      markedPrimePositionLine (((markedMemoryHistoryTraceState hZ history t).2.1 j k).1 : ℕ)
        (markedMemoryHistoryTraceState hZ history t).1.1
        (hZ _ (markedMemoryHistoryTraceState hZ history t).1.2)⟩ : MarkedMemoryAnchoredPrime) =
      markedMemoryHistoryTraceAddressAnchor hZ history a := by
  have h := markedMemoryHistoryTraceOrigin_anchor hZ history ha t (Sum.inl ⟨j,k⟩)
  rw [hi] at h
  exact h.symm

 theorem markedMemoryHistoryTrace_anchors_eq_of_prime_eq {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)
    (hempty : ∀ j, (s.2.2.1.1 j : ℕ) = 0) (hd : MarkedMemoryHistoryBirthDistinct hZ history)
    (r t : ℕ)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history r))
    (j : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t))
    (hp : markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history r) i =
      markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history t) j) :
    markedMemoryPopulationAnchor hZ (markedMemoryHistoryTraceState hZ history r) i =
      markedMemoryPopulationAnchor hZ (markedMemoryHistoryTraceState hZ history t) j := by
  have he : markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
        (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) r i =
      markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
        (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t j := by
    apply markedMemoryHistoryTraceAddressPrime_injective hZ history hempty hd
    exact (markedMemoryHistoryTraceOrigin_prime hZ history r i).trans
      (hp.trans (markedMemoryHistoryTraceOrigin_prime hZ history t j).symm)
  exact (markedMemoryHistoryTraceOrigin_anchor hZ history ha r i).symm.trans
    ((congrArg (markedMemoryHistoryTraceAddressAnchor hZ history) he).trans
      (markedMemoryHistoryTraceOrigin_anchor hZ history ha t j))

end
end ArtinMatthews
