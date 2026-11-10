module

public import ArtinMatthews.MarkedMemoryHistoryGhostOrigins
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact image and death set of a literal ghost choice. Only chosen old
pending indices disappear; every ordered birth gets its own target slot. -/
namespace ArtinMatthews
noncomputable section

def MarkedMemoryGhostOldSurvives {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P M B Z}
    (choice : MarkedMemoryGhostChoice hZ s) : MarkedMemoryPopulationIndex s → Prop :=
  Sum.elim (fun _ => True) (fun i => i.2 ∈ markedRawGhostSurvivors s.2.2 choice.deletion i.1)

theorem markedMemoryGhostOrigin_old_range {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) (old : MarkedMemoryPopulationIndex s) :
    Sum.inl old ∈ Set.range (markedMemoryGhostPopulationOrigin hZ s choice) ↔
      MarkedMemoryGhostOldSurvives choice old := by
  constructor
  · rintro ⟨i,hi⟩
    rcases i with ⟨j,k⟩ | ⟨j,k⟩
    · rw [markedMemoryGhostPopulationOrigin_active] at hi
      cases Sum.inl.inj hi
      trivial
    · obtain ⟨o,rfl⟩ := (markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j).symm.surjective k
      cases o with
      | inl survivor =>
        rw [markedMemoryGhostPopulationOrigin_old] at hi
        cases Sum.inl.inj hi
        exact survivor.2
      | inr birth =>
        rw [markedMemoryGhostPopulationOrigin_birth] at hi
        cases hi
  · intro h
    rcases old with ⟨j,k⟩ | ⟨j,k⟩
    · exact ⟨Sum.inl ⟨j,k⟩, markedMemoryGhostPopulationOrigin_active hZ s choice j k⟩
    · exact ⟨Sum.inr ⟨j,(markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes j).symm
        (Sum.inl ⟨k,h⟩)⟩, markedMemoryGhostPopulationOrigin_old hZ s choice j ⟨k,h⟩⟩

/-- Ghost deaths are exactly the actual selected old deletion indices. -/
theorem markedMemoryGhostOrigin_pending_death {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) (j : J) (k : Fin (s.2.2.1.1 j : ℕ)) :
    Sum.inl (Sum.inr ⟨j,k⟩) ∉ Set.range (markedMemoryGhostPopulationOrigin hZ s choice) ↔
      k ∈ choice.deletion j := by
  rw [markedMemoryGhostOrigin_old_range]
  simp [MarkedMemoryGhostOldSurvives, markedRawGhostSurvivors]

/-- Every performed indexed birth occurs in exactly one target slot. -/
theorem markedMemoryGhostOrigin_birth_range {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P M B Z)
    (choice : MarkedMemoryGhostChoice hZ s) (birth : MarkedMemoryGhostBirthIndex choice) :
    ∃! i, markedMemoryGhostPopulationOrigin hZ s choice i = Sum.inr birth := by
  refine ⟨Sum.inr ⟨birth.1,(markedMemoryGhostOrigin s.2.2 choice.deletion choice.sizes birth.1).symm
    (Sum.inr birth.2)⟩, markedMemoryGhostPopulationOrigin_birth hZ s choice birth.1 birth.2, ?_⟩
  intro i hi
  exact (markedMemoryGhostPopulationOrigin hZ s choice).injective
    (hi.trans (markedMemoryGhostPopulationOrigin_birth hZ s choice birth.1 birth.2).symm)

end
end ArtinMatthews
