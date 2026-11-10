module

public import ArtinMatthews.MarkedMemoryHistoryBirthIndices
public import ArtinMatthews.MarkedMemoryHistoryOrigins
public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsPopulation
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

/-! Actual population identities through a ghost choice. The injection
preserves old identities and gives a separate identity to every performed
birth, even when their numeric prime values coincide. -/
namespace ArtinMatthews

noncomputable def markedMemoryGhostPendingOrigin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) :
    (Σ j : J, Fin ((markedMemoryGhostChoiceTarget hZ s choice).2.2.1.1 j : ℕ)) ≃
      ((Σ j : J, ↥(markedRawGhostSurvivors s.2.2 choice.deletion j)) ⊕ MarkedMemoryGhostBirthIndex choice) :=
  (Equiv.sigmaCongrRight (fun j => markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j)).trans
    (Equiv.sigmaSumDistrib _ _)

noncomputable def markedMemoryGhostPopulationOrigin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) :
    MarkedMemoryPopulationIndex (markedMemoryGhostChoiceTarget hZ s choice) ↪
      (MarkedMemoryPopulationIndex s ⊕ MarkedMemoryGhostBirthIndex choice) :=
  ((Function.Embedding.sumMap (Function.Embedding.refl _) (markedMemoryGhostPendingOrigin hZ s choice).toEmbedding).trans
    (Equiv.sumAssoc _ _ _).symm.toEmbedding).trans
    (Function.Embedding.sumMap
      (Function.Embedding.sumMap (Function.Embedding.refl _)
        (Function.Embedding.sigmaMap (Function.Embedding.refl J)
          (fun _ => Function.Embedding.subtype _)))
      (Function.Embedding.refl _))

@[simp] theorem markedMemoryGhostPopulationOrigin_active {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) (j : J) (i : Fin M) :
    markedMemoryGhostPopulationOrigin hZ s choice (Sum.inl ⟨j,i⟩)=Sum.inl (Sum.inl ⟨j,i⟩) := rfl

/-- Plain indexed computation avoids any change to survivor enumeration. -/
theorem markedMemoryGhostPopulationOrigin_pending {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) (j : J)
    (i : Fin ((markedMemoryGhostChoiceTarget hZ s choice).2.2.1.1 j : ℕ)) :
    markedMemoryGhostPopulationOrigin hZ s choice (Sum.inr ⟨j,i⟩) =
      Sum.elim (fun old => Sum.inl (Sum.inr ⟨j,old.1⟩))
        (fun birth => Sum.inr ⟨j,birth⟩)
        (markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j i) := by
  change Sum.map
    (Sum.map id (fun old : Σ k : J, ↥(markedRawGhostSurvivors s.2.2 choice.deletion k) =>
      (⟨old.1,old.2.1⟩ : Σ k : J, Fin (s.2.2.1.1 k : ℕ)))) id
    (Sum.elim (fun old => Sum.inl (Sum.inr old)) Sum.inr
      (Sum.map
        (fun old => (⟨j,old⟩ : Σ k : J, ↥(markedRawGhostSurvivors s.2.2 choice.deletion k)))
        (fun birth => (⟨j,birth⟩ : MarkedMemoryGhostBirthIndex choice))
        (markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j i))) = _
  generalize ho : markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j i = o
  cases o <;> rfl

theorem markedMemoryGhostPopulationOrigin_old {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) (j : J)
    (i : ↥(markedRawGhostSurvivors s.2.2 choice.deletion j)) :
    markedMemoryGhostPopulationOrigin hZ s choice (Sum.inr
      ⟨j,(markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j).symm (Sum.inl i)⟩)=
      Sum.inl (Sum.inr ⟨j,i.1⟩) := by
  have h := markedMemoryGhostPopulationOrigin_pending hZ s choice j
    ((markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j).symm (Sum.inl i))
  simpa only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr] using h

theorem markedMemoryGhostPopulationOrigin_birth {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) (j : J) (i : Fin (choice.sizes.1 j : ℕ)) :
    markedMemoryGhostPopulationOrigin hZ s choice (Sum.inr
      ⟨j,(markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j).symm (Sum.inr i)⟩)=
      Sum.inr ⟨j,i⟩ := by
  have h := markedMemoryGhostPopulationOrigin_pending hZ s choice j
    ((markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j).symm (Sum.inr i))
  simpa only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr] using h

/-- Prime marks are transported along the actual identity injection.
Numeric distinctness is not a hypothesis. -/
theorem markedMemoryGhostPopulationOrigin_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s)
    (i : MarkedMemoryPopulationIndex (markedMemoryGhostChoiceTarget hZ s choice)) :
    Sum.elim (markedMemoryPopulationPrime s) (markedMemoryGhostBirthPrime choice)
        (markedMemoryGhostPopulationOrigin hZ s choice i)=
      markedMemoryPopulationPrime (markedMemoryGhostChoiceTarget hZ s choice) i := by
  rcases i with ⟨j,i⟩ | ⟨j,i⟩
  · rfl
  · obtain ⟨origin,rfl⟩ := (markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j).symm.surjective i
    cases origin with
    | inl old =>
      rw [markedMemoryGhostPopulationOrigin_old]
      change (s.2.2.2 j old.1).1.1=
        ((markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2) choice.deletion choice.sizes choice.births).2 j
          ((markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j).symm (Sum.inl old))).1.1
      rw [markedMemoryGhostOrigin_old]
    | inr birth =>
      rw [markedMemoryGhostPopulationOrigin_birth]
      change (choice.births j birth).1=
        ((markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2) choice.deletion choice.sizes choice.births).2 j
          ((markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j).symm (Sum.inr birth))).1.1
      rw [markedMemoryGhostOrigin_birth]
      rfl

end ArtinMatthews
