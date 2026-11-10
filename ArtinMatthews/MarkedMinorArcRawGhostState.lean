module

public import ArtinMatthews.MarkedMinorArcDirtyPending
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

/-! Literal signed-ghost state transition from PD §4: delete chosen indexed
old hits, keep all other indexed particles, then append an ordered batch
of actual prime labels anchored at the current projective residues. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Actual indexed deletion masks, allowing repeated particle values. -/
abbrev MarkedRawGhostDeletion {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {B : ℕ}
    (m : MarkedRawMemory P B) := (j : J) → Finset (Fin (m.1.1 j : ℕ))

/-- Literal surviving old indices in their original increasing order. -/
def markedRawGhostSurvivors {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {B : ℕ}
    (m : MarkedRawMemory P B) (del : MarkedRawGhostDeletion m) (j : J) :
    Finset (Fin (m.1.1 j : ℕ)) := Finset.univ \ del j

/-- The actual rule only deletes old particles hitting the current position. -/
def MarkedRawGhostDeletionAllowed {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m) : Prop :=
  ∀ j, del j ⊆ markedRawGroupHitIndices m j z hz

/-- Ordered birth lengths which remain in the literal total memory cutoff. -/
abbrev MarkedRawGhostBirthSizes {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) (del : MarkedRawGhostDeletion m) :=
  {l : J → Fin (B+1) // ∑ j, ((markedRawGhostSurvivors m del j).card+(l j : ℕ)) ≤ B}

/-- Births are actual band primes, before attaching their current anchor. -/
abbrev MarkedRawGhostBirthLabels {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B} {del : MarkedRawGhostDeletion m}
    (l : MarkedRawGhostBirthSizes m del) := (j : J) → Fin (l.1 j : ℕ) → ↥(P j)

/-- A genuine newly born particle, with counting-measure anchor at [z]_p. -/
def markedRawAnchoredParticle (P : Finset Nat.Primes) (p : P)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) : MarkedRawParticle P :=
  ⟨p,markedPrimePositionLine (p.1 : ℕ) z hz⟩

theorem markedRawAnchoredParticle_hits (P : Finset Nat.Primes) (p : P)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    MarkedRawParticleHits P z hz (markedRawAnchoredParticle P p z hz) := rfl

/-- Actual target sizes after deletion and birth, in the same total cutoff. -/
def markedRawGhostTargetSizes {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) : MarkedRawMemorySizes J B :=
  ⟨fun j => ⟨(markedRawGhostSurvivors m del j).card+(l.1 j : ℕ),by
      have hh := (Finset.single_le_sum (fun i _ => Nat.zero_le
        ((markedRawGhostSurvivors m del i).card+(l.1 i : ℕ))) (Finset.mem_univ j)).trans l.2
      omega⟩,l.2⟩

/-- Literal target memory: surviving indexed old particles, then ordered
new particles with actual current anchors. No particle distinctness is added. -/
noncomputable def markedRawGhostTargetMemory {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) : MarkedRawMemory P B :=
  ⟨markedRawGhostTargetSizes m del l,fun j => Fin.addCases
    (fun k => m.2 j ((markedRawGhostSurvivors m del j).orderEmbOfFin rfl k))
    (fun k => markedRawAnchoredParticle (P j) (births j k) z hz)⟩

/-- Actual full ghost state leaves the physical position and all active
slots unchanged, acting only on literal indexed pending memory. -/
noncomputable def markedRawGhostTargetState {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (del : MarkedRawGhostDeletion s.2.2) (l : MarkedRawGhostBirthSizes s.2.2 del)
    (births : MarkedRawGhostBirthLabels l) : MarkedRawState P M B Z :=
  (s.1,(s.2.1,markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2) del l births))

theorem markedRawGhostTargetState_position {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (del : MarkedRawGhostDeletion s.2.2) (l : MarkedRawGhostBirthSizes s.2.2 del)
    (births : MarkedRawGhostBirthLabels l) : (markedRawGhostTargetState hZ s del l births).1=s.1 := rfl

theorem markedRawGhostTargetState_active {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (del : MarkedRawGhostDeletion s.2.2) (l : MarkedRawGhostBirthSizes s.2.2 del)
    (births : MarkedRawGhostBirthLabels l) : (markedRawGhostTargetState hZ s del l births).2.1=s.2.1 := rfl

/-- The total-size restriction is literally preserved by the transition. -/
theorem markedRawGhostTargetMemory_total_le {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) :
    (∑ j, ((markedRawGhostTargetMemory m z hz del l births).1.1 j : ℕ)) ≤ B := l.2

end ArtinMatthews
