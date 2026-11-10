module

public import ArtinMatthews.MarkedMemoryHistoryGhostOrigins
public import ArtinMatthews.MarkedMemoryHistorySlotOrigins
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

/-! Literal population marks include the prime and its projective anchor.
Active entries carry the current position's line; pending entries retain
the stored line. Equal primes with different anchors are kept distinct. -/
namespace ArtinMatthews
noncomputable section

abbrev MarkedMemoryAnchoredPrime := Σ p : Nat.Primes, MarkedRawPrimeLine p

def markedMemoryForgetBandParticle {P : Finset Nat.Primes}
    (a : MarkedRawParticle P) : MarkedMemoryAnchoredPrime := ⟨a.1.1,a.2⟩

def markedMemoryPopulationAnchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z) :
    MarkedMemoryPopulationIndex s → MarkedMemoryAnchoredPrime :=
  Sum.elim (fun i => ⟨(s.2.1 i.1 i.2).1,
    markedPrimePositionLine ((s.2.1 i.1 i.2).1 : ℕ) s.1.1 (hZ _ s.1.2)⟩)
    (fun i => markedMemoryForgetBandParticle (s.2.2.2 i.1 i.2))

def markedMemoryGhostBirthAnchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P M B Z}
    (choice : MarkedMemoryGhostChoice hZ s) (birth : MarkedMemoryGhostBirthIndex choice) :
    MarkedMemoryAnchoredPrime :=
  ⟨markedMemoryGhostBirthPrime choice birth,
    markedPrimePositionLine (markedMemoryGhostBirthPrime choice birth : ℕ) s.1.1 (hZ _ s.1.2)⟩

/-- Actual slot reindexing preserves the full prime-and-anchor mark. -/
theorem markedMemorySlotPopulationEquiv_anchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (σ : J → Equiv.Perm (Fin M))
    (s : MarkedRawState P M B Z) (i : MarkedMemoryPopulationIndex (markedRawSlotEquiv σ s)) :
    markedMemoryPopulationAnchor hZ s (markedMemorySlotPopulationEquiv σ s i) =
      markedMemoryPopulationAnchor hZ (markedRawSlotEquiv σ s) i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩ <;> rfl

/-- The ghost's ordered births are anchored at the actual current position;
old survivors retain their stored anchor exactly. -/
theorem markedMemoryGhostPopulationOrigin_anchor {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s)
    (i : MarkedMemoryPopulationIndex (markedMemoryGhostChoiceTarget hZ s choice)) :
    Sum.elim (markedMemoryPopulationAnchor hZ s) (markedMemoryGhostBirthAnchor choice)
      (markedMemoryGhostPopulationOrigin hZ s choice i) =
        markedMemoryPopulationAnchor hZ (markedMemoryGhostChoiceTarget hZ s choice) i := by
  rcases i with ⟨j,k⟩ | ⟨j,k⟩
  · rfl
  · obtain ⟨o,rfl⟩ := (markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j).symm.surjective k
    cases o with
    | inl old =>
      rw [markedMemoryGhostPopulationOrigin_old]
      exact congrArg markedMemoryForgetBandParticle
        (markedMemoryGhostOrigin_old s.2.2 s.1.1 (hZ _ s.1.2) choice.deletion choice.sizes choice.births j old).symm
    | inr birth =>
      rw [markedMemoryGhostPopulationOrigin_birth]
      exact congrArg markedMemoryForgetBandParticle
        (markedMemoryGhostOrigin_birth s.2.2 s.1.1 (hZ _ s.1.2) choice.deletion choice.sizes choice.births j birth).symm

end
end ArtinMatthews
