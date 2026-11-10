module

public import ArtinMatthews.MarkedMemoryHistoryTraceBirths
public import ArtinMatthews.MarkedMemoryHistoryVisits
public import ArtinMatthews.MarkedMemoryHistoryPresence
public import ArtinMatthews.MarkedMemoryHistoryPresenceIntervals
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

/-! No resurrection and genuine finite lifespan intervals for the actual
chronological ghost/edge histories. Prime values identify indexed births only
under the separately stated global distinctness and initial boundary. -/
namespace ArtinMatthews
noncomputable section

abbrev MarkedMemoryHistoryTracePopulation {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ) :=
  MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t)

abbrev MarkedMemoryHistoryTraceAddress {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :=
  MarkedMemoryLineageAddress (fun t => MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t))
    (MarkedMemoryHistoryTraceBirth hZ history)

def markedMemoryHistoryTraceAddressPrime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) : MarkedMemoryHistoryTraceAddress hZ history → Nat.Primes :=
  Sum.elim (markedMemoryPopulationPrime s)
    (fun b => markedMemoryHistoryTraceBirthPrime hZ history b.1 b.2)

def markedMemoryHistoryTraceAddressEquiv {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0) :
    MarkedMemoryHistoryTraceAddress hZ history ≃ MarkedMemoryHistoryAddress hZ history :=
  Equiv.sumCongr (markedMemoryEmptyPopulationEquiv s hempty) (markedMemoryHistoryTraceBirthEquiv hZ history)

theorem markedMemoryHistoryTraceAddressEquiv_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryHistoryAddressPrime hZ history (markedMemoryHistoryTraceAddressEquiv hZ history hempty a) =
      markedMemoryHistoryTraceAddressPrime hZ history a := by
  cases a with
  | inl old => exact markedMemoryEmptyPopulationEquiv_prime s hempty old
  | inr birth => exact markedMemoryHistoryTraceBirthEquiv_prime hZ history birth

theorem markedMemoryHistoryTraceAddressPrime_injective {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) :
    Function.Injective (markedMemoryHistoryTraceAddressPrime hZ history) := by
  intro a b hab
  apply (markedMemoryHistoryTraceAddressEquiv hZ history hempty).injective
  apply hd
  exact (markedMemoryHistoryTraceAddressEquiv_prime hZ history hempty a).trans
    (hab.trans (markedMemoryHistoryTraceAddressEquiv_prime hZ history hempty b).symm)

/-- The generic recursive lineage is instantiated with the genuine local transitions. -/
theorem markedMemoryHistoryTraceOrigin_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : ℕ)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryTraceState hZ history t)) :
    markedMemoryHistoryTraceAddressPrime hZ history
      (markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t i) =
        markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history t) i :=
  markedMemoryLineageOrigin_mark (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
    (fun t => markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history t))
    (markedMemoryHistoryTraceBirthPrime hZ history)
    (markedMemoryHistoryTraceStep_prime hZ history) t i

/-- Occurrence of a prime is occurrence of its unique actual birth identity. -/
theorem markedMemoryHistoryTrace_present_iff_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (a : MarkedMemoryHistoryTraceAddress hZ history) (t : ℕ) :
    MarkedMemoryLineagePresent (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t a ↔
      ∃ i, markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history t) i =
        markedMemoryHistoryTraceAddressPrime hZ history a := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,(markedMemoryHistoryTraceOrigin_prime hZ history t i).symm.trans
      (congrArg (markedMemoryHistoryTraceAddressPrime hZ history) hi)⟩
  · rintro ⟨i,hi⟩
    refine ⟨i,markedMemoryHistoryTraceAddressPrime_injective hZ history hempty hd ?_⟩
    exact (markedMemoryHistoryTraceOrigin_prime hZ history t i).trans hi

/-- An actual prime cannot disappear from both active and pending memory
and later reappear in a birth-distinct history. -/
theorem markedMemoryHistory_prime_no_resurrection {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (p : Nat.Primes) {r u t : ℕ}
    (hr : ∃ i, markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history r) i = p)
    (ht : ∃ i, markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history t) i = p)
    (hru : r ≤ u) (hut : u ≤ t) :
    ∃ i, markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history u) i = p := by
  obtain ⟨i,hi⟩ := hr
  let a := markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) r i
  have hap : markedMemoryHistoryTraceAddressPrime hZ history a = p :=
    (markedMemoryHistoryTraceOrigin_prime hZ history r i).trans hi
  have hrt : MarkedMemoryLineagePresent (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) r a := ⟨i,rfl⟩
  have htt := (markedMemoryHistoryTrace_present_iff_prime hZ history hempty hd a t).mpr
    (by simpa only [hap] using ht)
  have hu := markedMemoryLineagePresent_no_resurrection (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) hrt htt hru hut
  simpa only [hap] using (markedMemoryHistoryTrace_present_iff_prime hZ history hempty hd a u).mp hu

/-- Genuine finite lifespan endpoints, computed from the actual occurrence
set on all ghost/edge populations up to the terminal ghost. -/
theorem markedMemoryHistory_prime_finite_lifespan {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (hempty : ∀ j, (s.2.2.1.1 j : ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (p : Nat.Primes)
    (hp : ∃ t ≤ 2*n+1, ∃ i, markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history t) i = p) :
    ∃ first last, first ≤ last ∧ last ≤ 2*n+1 ∧ ∀ t,
      (t ≤ 2*n+1 ∧ ∃ i, markedMemoryPopulationPrime (markedMemoryHistoryTraceState hZ history t) i = p) ↔
        first ≤ t ∧ t ≤ last := by
  obtain ⟨t,ht,i,hi⟩ := hp
  let a := markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) t i
  have hap : markedMemoryHistoryTraceAddressPrime hZ history a = p :=
    (markedMemoryHistoryTraceOrigin_prime hZ history t i).trans hi
  obtain ⟨last,hl,hbl,hiff⟩ := markedMemoryLineagePresence_finite_lifespan
    (markedMemoryHistoryTraceStep hZ history) (2*n+1) a ⟨t,ht,i,rfl⟩
  refine ⟨markedMemoryLineageBirthTime a,last,hbl,hl,?_⟩
  intro u
  have he := hiff u
  rw [markedMemoryHistoryTrace_present_iff_prime hZ history hempty hd a u, hap] at he
  exact he

end
end ArtinMatthews
