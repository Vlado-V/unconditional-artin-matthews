module

public import ArtinMatthews.MarkedMemoryRunReconstruction
public import ArtinMatthews.MarkedMemoryHistoryGroups
public import ArtinMatthews.MarkedMemoryLineageLabelEndpoints
public import ArtinMatthews.MarkedMemoryHistoryLifespans
public import ArtinMatthews.MarkedMemoryHistoryTraceComplete
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

/-! Decorated lifespan/run data and its actual reconstruction. Input
coordinates are the independently admissible local run events, injected
active/pending identity labels and nonempty finite intervals. A history is
constructed from the events; no history, address bijection or endpoint
identification is supplied as a premise. Slot and birth order decorations
remain explicit in the local event data. -/
namespace ArtinMatthews
noncomputable section

universe u w
variable {J : Type u} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)

structure MarkedMemoryLifespanRunData (A : Type w) where
  events : MarkedMemoryRunHistory hZ n s
  ids : (t : ℕ) → MarkedMemoryHistoryTracePopulation hZ (markedMemoryRunHistoryReconstruct hZ events) t ↪ A
  born : (t : ℕ) → MarkedMemoryHistoryTraceBirth hZ (markedMemoryRunHistoryReconstruct hZ events) t → A
  first : A → ℕ
  last : A → ℕ
  prime : A → Nat.Primes
  group : A → J
  step_labels : ∀ t x, Sum.elim (ids t) (born t)
      (markedMemoryHistoryTraceStep hZ (markedMemoryRunHistoryReconstruct hZ events) t x) = ids (t+1) x
  genuine_birth : ∀ t b, first (born t b) = t+1
  nonempty : ∀ a, first a ≤ last a
  bounded : ∀ a, last a ≤ 2*n+1
  present : ∀ a t, t ≤ 2*n+1 → ((∃ x, ids t x = a) ↔ first a ≤ t ∧ t ≤ last a)
  prime_labels : ∀ t x, prime (ids t x) =
    markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ (markedMemoryRunHistoryReconstruct hZ events) t) x
  group_labels : ∀ t x, group (ids t x) =
    markedMemoryPopulationGroup (markedMemoryHistoryTraceState hZ (markedMemoryRunHistoryReconstruct hZ events) t) x

def markedMemoryLifespanRunReconstruct {A : Type w} (d : MarkedMemoryLifespanRunData hZ s (n := n) A) :
    MarkedMemoryChronologicalHistory hZ n s := markedMemoryRunHistoryReconstruct hZ d.events

def markedMemoryLifespanRunAddressEquiv {A : Type w} (d : MarkedMemoryLifespanRunData hZ s (n := n) A) :
    MarkedMemoryHistoryTraceAddress hZ (markedMemoryLifespanRunReconstruct hZ s d) ≃ A :=
  markedMemoryLineageIntervalTraceEquiv
    (markedMemoryHistoryTraceStep hZ (markedMemoryLifespanRunReconstruct hZ s d)) (2*n+1)
    d.ids d.born d.first d.last d.step_labels d.genuine_birth d.nonempty d.bounded d.present
    (fun t b => (markedMemoryHistoryTraceStep_birth_range hZ (markedMemoryLifespanRunReconstruct hZ s d) t b).exists)

theorem markedMemoryLifespanRunAddressEquiv_origin {A : Type w}
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A) (t : ℕ)
    (i : MarkedMemoryHistoryTracePopulation hZ (markedMemoryLifespanRunReconstruct hZ s d) t) :
    markedMemoryLifespanRunAddressEquiv hZ s d
      (markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ (markedMemoryLifespanRunReconstruct hZ s d))
        (Birth := MarkedMemoryHistoryTraceBirth hZ (markedMemoryLifespanRunReconstruct hZ s d))
        (markedMemoryHistoryTraceStep hZ (markedMemoryLifespanRunReconstruct hZ s d)) t i) = d.ids t i :=
  markedMemoryLineageLabel_origin _ d.ids d.born d.step_labels t i

theorem markedMemoryLifespanRunAddressEquiv_first {A : Type w}
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A)
    (a : MarkedMemoryHistoryTraceAddress hZ (markedMemoryLifespanRunReconstruct hZ s d)) :
    markedMemoryLineageBirthTime a = d.first (markedMemoryLifespanRunAddressEquiv hZ s d a) :=
  markedMemoryLineageIntervalTraceEquiv_birth _ (2*n+1) d.ids d.born d.first d.last
    d.step_labels d.genuine_birth d.nonempty d.bounded d.present _ a

theorem markedMemoryLifespanRunAddressEquiv_last {A : Type w}
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A)
    (a : MarkedMemoryHistoryTraceAddress hZ (markedMemoryLifespanRunReconstruct hZ s d)) :
    markedMemoryHistoryLifespanLast hZ (markedMemoryLifespanRunReconstruct hZ s d) a =
      d.last (markedMemoryLifespanRunAddressEquiv hZ s d a) :=
  markedMemoryLineageIntervalTraceEquiv_last _ (2*n+1) d.ids d.born d.first d.last
    d.step_labels d.genuine_birth d.nonempty d.bounded d.present _ a

theorem markedMemoryLifespanRunAddressEquiv_prime {A : Type w}
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A)
    (a : MarkedMemoryHistoryTraceAddress hZ (markedMemoryLifespanRunReconstruct hZ s d)) :
    d.prime (markedMemoryLifespanRunAddressEquiv hZ s d a) =
      markedMemoryHistoryTraceAddressPrime hZ (markedMemoryLifespanRunReconstruct hZ s d) a := by
  obtain ⟨t,_,i,hi⟩ := markedMemoryHistoryTraceAddress_present hZ (markedMemoryLifespanRunReconstruct hZ s d) a
  rw [← hi, markedMemoryLifespanRunAddressEquiv_origin]
  exact (d.prime_labels t i).trans
    (markedMemoryHistoryTraceOrigin_prime hZ (markedMemoryLifespanRunReconstruct hZ s d) t i).symm

theorem markedMemoryLifespanRunAddressEquiv_group {A : Type w}
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A)
    (a : MarkedMemoryHistoryTraceAddress hZ (markedMemoryLifespanRunReconstruct hZ s d)) :
    d.group (markedMemoryLifespanRunAddressEquiv hZ s d a) =
      markedMemoryHistoryTraceAddressGroup hZ (markedMemoryLifespanRunReconstruct hZ s d) a := by
  obtain ⟨t,_,i,hi⟩ := markedMemoryHistoryTraceAddress_present hZ (markedMemoryLifespanRunReconstruct hZ s d) a
  rw [← hi, markedMemoryLifespanRunAddressEquiv_origin]
  exact (d.group_labels t i).trans
    (markedMemoryHistoryTraceOrigin_group hZ (markedMemoryLifespanRunReconstruct hZ s d) t i).symm

/-- Reconstructing any admissible decorated lifespan data recovers exactly
its original local run events, including slot and birth order choices. -/
theorem markedMemoryLifespanRunReconstruct_events {A : Type w}
    (d : MarkedMemoryLifespanRunData hZ s (n := n) A) :
    markedMemoryRunHistoryEquiv hZ n s (markedMemoryLifespanRunReconstruct hZ s d) = d.events :=
  markedMemoryRunHistory_encode_reconstruct hZ d.events

/-- Canonical finite lifespan data can be computed from every local run
history. This constructor supplies proofs from the genuine trace. -/
def markedMemoryCanonicalLifespanRunData (events : MarkedMemoryRunHistory hZ n s) :
    MarkedMemoryLifespanRunData hZ s (n := n)
      (MarkedMemoryHistoryTraceAddress hZ (markedMemoryRunHistoryReconstruct hZ events)) where
  events := events
  ids t :=
    ⟨markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ (markedMemoryRunHistoryReconstruct hZ events))
      (Birth := MarkedMemoryHistoryTraceBirth hZ (markedMemoryRunHistoryReconstruct hZ events))
      (markedMemoryHistoryTraceStep hZ (markedMemoryRunHistoryReconstruct hZ events)) t,
      markedMemoryLineageOrigin_injective _ t⟩
  born t b := Sum.inr ⟨t,b⟩
  first := markedMemoryLineageBirthTime
  last := markedMemoryHistoryLifespanLast hZ (markedMemoryRunHistoryReconstruct hZ events)
  prime := markedMemoryHistoryTraceAddressPrime hZ (markedMemoryRunHistoryReconstruct hZ events)
  group := markedMemoryHistoryTraceAddressGroup hZ (markedMemoryRunHistoryReconstruct hZ events)
  step_labels _ _ := rfl
  genuine_birth _ _ := rfl
  nonempty a := (markedMemoryHistory_lifespan_bounds hZ (markedMemoryRunHistoryReconstruct hZ events) a).1
  bounded a := (markedMemoryHistory_lifespan_bounds hZ (markedMemoryRunHistoryReconstruct hZ events) a).2
  present a t ht := by
    constructor
    · intro hp
      exact (markedMemoryHistory_lifespan_exact hZ (markedMemoryRunHistoryReconstruct hZ events) a t).mp ⟨ht,hp⟩
    · intro hp
      exact ((markedMemoryHistory_lifespan_exact hZ (markedMemoryRunHistoryReconstruct hZ events) a t).mpr hp).2
  prime_labels t i := markedMemoryHistoryTraceOrigin_prime hZ (markedMemoryRunHistoryReconstruct hZ events) t i
  group_labels t i := markedMemoryHistoryTraceOrigin_group hZ (markedMemoryRunHistoryReconstruct hZ events) t i

theorem markedMemoryCanonicalLifespanRunData_reconstruct (events : MarkedMemoryRunHistory hZ n s) :
    markedMemoryLifespanRunReconstruct hZ s (markedMemoryCanonicalLifespanRunData hZ s events) =
      markedMemoryRunHistoryReconstruct hZ events := rfl

theorem markedMemoryCanonicalLifespanRunData_address (events : MarkedMemoryRunHistory hZ n s)
    (a : MarkedMemoryHistoryTraceAddress hZ (markedMemoryRunHistoryReconstruct hZ events)) :
    markedMemoryLifespanRunAddressEquiv hZ s (markedMemoryCanonicalLifespanRunData hZ s events) a = a := by
  cases a <;> rfl

/-- Every literal chronological history is reconstructed from admissible
computed lifespan/run data; the statement assumes no correspondence. -/
theorem markedMemoryHistory_covered_by_lifespan_data (history : MarkedMemoryChronologicalHistory hZ n s) :
    ∃ d : MarkedMemoryLifespanRunData hZ s (n := n)
      (MarkedMemoryHistoryTraceAddress hZ
        (markedMemoryRunHistoryReconstruct hZ (markedMemoryRunHistoryEquiv hZ n s history))),
      markedMemoryLifespanRunReconstruct hZ s d = history := by
  refine ⟨markedMemoryCanonicalLifespanRunData hZ s (markedMemoryRunHistoryEquiv hZ n s history),?_⟩
  exact markedMemoryRunHistory_reconstruct_encode hZ history

end
end ArtinMatthews
