module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalar
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

/-! A deleted old scalar is located at the actual last occurrence of its
identity, while a birth scalar is at its actual first occurrence. Old
survivors cross the genuine ghost transition. -/
namespace ArtinMatthews
noncomputable section

theorem markedMemoryLineage_dead_not_present {T : ℕ → Type*} {Birth : ℕ → Type*}
    (step : ∀ t, T (t+1) ↪ T t ⊕ Birth t) (t : ℕ) (old : T t)
    (hd : Sum.inl old ∉ Set.range (step t)) :
    ¬MarkedMemoryLineagePresent step (t+1) (markedMemoryLineageOrigin step t old) := by
  rintro ⟨next, hn⟩
  change Sum.elim (markedMemoryLineageOrigin step t) (fun b => Sum.inr ⟨t,b⟩) (step t next) = _ at hn
  generalize hs : step t next = origin at hn
  cases origin with
  | inl previous =>
    simp only [Sum.elim_inl] at hn
    have he := markedMemoryLineageOrigin_injective step t hn
    exact hd ⟨next, hs.trans (congrArg Sum.inl he)⟩
  | inr birth =>
    simp only [Sum.elim_inr] at hn
    have htime := congrArg markedMemoryLineageBirthTime hn
    have hle := markedMemoryLineageOrigin_birthTime_le step t old
    change t+1 = _ at htime
    omega

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryHistoryGhostTarget_trace (v : Fin (n+1)) :
    markedMemoryHistoryTraceState hZ history (markedMemoryHistoryGhostTime n v+1) =
      markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v)
        (markedMemoryHistoryVertexGhost hZ history v) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun w => ?_) v
    · rfl
    · exact ih history.2.2 w

def markedMemoryHistoryGhostTargetIndex (v : Fin (n+1))
    (i : MarkedMemoryPopulationIndex
      (markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v)
        (markedMemoryHistoryVertexGhost hZ history v))) :
    MarkedMemoryHistoryTracePopulation hZ history (markedMemoryHistoryGhostTime n v+1) :=
  cast (congrArg MarkedMemoryPopulationIndex (markedMemoryHistoryGhostTarget_trace hZ history v)).symm i

theorem markedMemoryHistoryGhostTargetIndex_surjective (v : Fin (n+1)) :
    Function.Surjective (markedMemoryHistoryGhostTargetIndex hZ history v) :=
  (Equiv.cast (congrArg MarkedMemoryPopulationIndex
    (markedMemoryHistoryGhostTarget_trace hZ history v)).symm).surjective

theorem markedMemoryHistoryGhostSourceIndex_injective (v : Fin (n+1)) :
    Function.Injective (markedMemoryHistoryGhostSourceIndex hZ history v) :=
  (Equiv.cast (congrArg MarkedMemoryPopulationIndex
    (markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n v))).symm).injective

theorem markedMemoryHistoryGhostStep (v : Fin (n+1))
    (i : MarkedMemoryPopulationIndex
      (markedMemoryGhostChoiceTarget hZ (markedMemoryHistoryVertexState hZ history v)
        (markedMemoryHistoryVertexGhost hZ history v))) :
    markedMemoryHistoryTraceStep hZ history (markedMemoryHistoryGhostTime n v)
        (markedMemoryHistoryGhostTargetIndex hZ history v i) =
      Sum.map (markedMemoryHistoryGhostSourceIndex hZ history v)
        (markedMemoryHistoryGhostTraceBirth hZ history v)
        (markedMemoryGhostPopulationOrigin hZ (markedMemoryHistoryVertexState hZ history v)
          (markedMemoryHistoryVertexGhost hZ history v) i) := by
  induction n generalizing s with
  | zero =>
    change markedMemoryGhostPopulationOrigin hZ s history i =
      Sum.map id id (markedMemoryGhostPopulationOrigin hZ s history i)
    cases markedMemoryGhostPopulationOrigin hZ s history i <;> rfl
  | succ n ih =>
    revert i
    refine Fin.cases ?_ (fun w => ?_) v
    · intro i
      change markedMemoryGhostPopulationOrigin hZ s history.1 i =
        Sum.map id id (markedMemoryGhostPopulationOrigin hZ s history.1 i)
      cases markedMemoryGhostPopulationOrigin hZ s history.1 i <;> rfl
    · intro i; exact ih history.2.2 w i

theorem markedMemoryHistoryGhost_deleted (v : Fin (n+1)) (band : J)
    (k : Fin ((markedMemoryHistoryVertexState hZ history v).2.2.1.1 band : ℕ))
    (hk : k ∈ (markedMemoryHistoryVertexGhost hZ history v).deletion band) :
    Sum.inl (markedMemoryHistoryGhostSourceIndex hZ history v (Sum.inr ⟨band,k⟩)) ∉
      Set.range (markedMemoryHistoryTraceStep hZ history (markedMemoryHistoryGhostTime n v)) := by
  have hd := (markedMemoryGhostOrigin_pending_death hZ (markedMemoryHistoryVertexState hZ history v)
    (markedMemoryHistoryVertexGhost hZ history v) band k).mpr hk
  rintro ⟨next, hn⟩
  obtain ⟨i, rfl⟩ := markedMemoryHistoryGhostTargetIndex_surjective hZ history v next
  rw [markedMemoryHistoryGhostStep] at hn
  generalize ho : markedMemoryGhostPopulationOrigin hZ (markedMemoryHistoryVertexState hZ history v)
    (markedMemoryHistoryVertexGhost hZ history v) i = o at hn
  cases o with
  | inl old =>
    simp only [Sum.map_inl] at hn
    have he := markedMemoryHistoryGhostSourceIndex_injective hZ history v (Sum.inl.inj hn)
    exact hd ⟨i, ho.trans (congrArg Sum.inl he)⟩
  | inr birth => cases hn

theorem markedMemoryHistoryGhost_deleted_last (v : Fin (n+1)) (band : J)
    (k : Fin ((markedMemoryHistoryVertexState hZ history v).2.2.1.1 band : ℕ))
    (hk : k ∈ (markedMemoryHistoryVertexGhost hZ history v).deletion band) :
    markedMemoryHistoryLifespanLast hZ history
      (markedMemoryHistoryGhostSourceOrigin hZ history v (Sum.inr ⟨band,k⟩)) =
        markedMemoryHistoryGhostTime n v := by
  let a := markedMemoryHistoryGhostSourceOrigin hZ history v (Sum.inr ⟨band,k⟩)
  have ht : markedMemoryHistoryGhostTime n v ≤ 2*n+1 := by
    rw [markedMemoryHistoryGhostTime_eq]
    have hv := v.isLt
    omega
  have hp := (markedMemoryHistory_lifespan_exact hZ history a (markedMemoryHistoryGhostTime n v)).mp
    ⟨ht, markedMemoryHistoryGhostSourceIndex hZ history v (Sum.inr ⟨band,k⟩), rfl⟩
  have hd := markedMemoryLineage_dead_not_present (markedMemoryHistoryTraceStep hZ history)
    (markedMemoryHistoryGhostTime n v)
    (markedMemoryHistoryGhostSourceIndex hZ history v (Sum.inr ⟨band,k⟩))
    (markedMemoryHistoryGhost_deleted hZ history v band k hk)
  apply le_antisymm ?_ hp.2
  by_contra hn
  have hn' : markedMemoryHistoryGhostTime n v+1 ≤ markedMemoryHistoryLifespanLast hZ history a := by omega
  exact hd ((markedMemoryHistory_lifespan_exact hZ history a
    (markedMemoryHistoryGhostTime n v+1)).mpr ⟨by omega, hn'⟩).2

theorem markedMemoryHistoryGhost_birth_first (v : Fin (n+1))
    (birth : MarkedMemoryGhostBirthIndex (markedMemoryHistoryVertexGhost hZ history v)) :
    markedMemoryLineageBirthTime
      (markedMemoryHistoryGhostScalarOrigin hZ history ⟨v, Sum.inr birth⟩) =
        markedMemoryHistoryGhostTime n v+1 := rfl

end
end ArtinMatthews
