module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalar
public import ArtinMatthews.MarkedMemoryHistoryPrimewise
public import ArtinMatthews.MarkedMemoryHistoryTraceAnchors
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ghost scalar events are the literal signed endpoint and
internal damping factors of the primewise line expansion. The comparison
uses the carried anchor of each indexed identity, not a numeric-prime
identification or an assumed scalar-product correspondence. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryAnchoredPrimeHits (a : MarkedMemoryAnchoredPrime)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) : Prop :=
  a.2 = markedPrimePositionLine (a.1 : ℕ) z hz

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryPopulationAnchor_cast (s t : MarkedRawState P (pads+1) B Z)
    (hst : s = t) (i : MarkedMemoryPopulationIndex t) :
    markedMemoryPopulationAnchor hZ s (cast (congrArg MarkedMemoryPopulationIndex hst).symm i) =
      markedMemoryPopulationAnchor hZ t i := by
  subst t
  rfl

variable {s : MarkedRawState P (pads+1) B Z} (history : MarkedMemoryChronologicalHistory hZ n s)

def markedMemoryHistoryAddressLineHit (a : MarkedMemoryHistoryTraceAddress hZ history)
    (v : Fin (n+1)) : ℝ :=
  if markedMemoryAnchoredPrimeHits (markedMemoryHistoryTraceAddressAnchor hZ history a)
    (markedMemoryHistoryVertexPositions hZ history v) (markedMemoryHistoryVertexPrimitive hZ history v)
  then 1 else 0

theorem markedMemoryHistoryGhostSourceOrigin_anchor
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (v : Fin (n+1))
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryVertexState hZ history v)) :
    markedMemoryHistoryTraceAddressAnchor hZ history (markedMemoryHistoryGhostSourceOrigin hZ history v i) =
      markedMemoryPopulationAnchor hZ (markedMemoryHistoryVertexState hZ history v) i := by
  exact (markedMemoryHistoryTraceOrigin_anchor hZ history ha _
    (markedMemoryHistoryGhostSourceIndex hZ history v i)).trans
      (markedMemoryPopulationAnchor_cast hZ _ _
        (markedMemoryHistoryTraceState_stage hZ history (markedMemoryHistoryVertexStage n v)) i)

theorem markedMemoryHistoryGhostTraceBirth_anchor (v : Fin (n+1))
    (birth : MarkedMemoryGhostBirthIndex (markedMemoryHistoryVertexGhost hZ history v)) :
    markedMemoryHistoryTraceBirthAnchor hZ history (markedMemoryHistoryGhostTime n v)
      (markedMemoryHistoryGhostTraceBirth hZ history v birth) =
        markedMemoryGhostBirthAnchor (markedMemoryHistoryVertexGhost hZ history v) birth := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    revert birth
    refine Fin.cases ?_ (fun w => ?_) v
    · intro birth; rfl
    · intro birth; exact ih history.2.2 w birth

theorem markedMemoryHistoryGhostPending_hit_iff
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (v : Fin (n+1))
    (band : J) (k : Fin ((markedMemoryHistoryVertexState hZ history v).2.2.1.1 band : ℕ)) :
    k ∈ markedRawGroupHitIndices (markedMemoryHistoryVertexState hZ history v).2.2 band
        (markedMemoryHistoryVertexState hZ history v).1.1
        (hZ _ (markedMemoryHistoryVertexState hZ history v).1.2) ↔
      markedMemoryAnchoredPrimeHits
        (markedMemoryHistoryTraceAddressAnchor hZ history
          (markedMemoryHistoryGhostSourceOrigin hZ history v (Sum.inr ⟨band,k⟩)))
        (markedMemoryHistoryVertexPositions hZ history v) (markedMemoryHistoryVertexPrimitive hZ history v) := by
  rw [markedMemoryHistoryGhostSourceOrigin_anchor hZ history ha]
  simp only [markedRawGroupHitIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem markedMemoryHistoryGhostPending_lineHit
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (v : Fin (n+1))
    (band : J) (k : Fin ((markedMemoryHistoryVertexState hZ history v).2.2.1.1 band : ℕ)) :
    markedMemoryHistoryAddressLineHit hZ history
        (markedMemoryHistoryGhostSourceOrigin hZ history v (Sum.inr ⟨band,k⟩)) v =
      if k ∈ markedRawGroupHitIndices (markedMemoryHistoryVertexState hZ history v).2.2 band
        (markedMemoryHistoryVertexState hZ history v).1.1
        (hZ _ (markedMemoryHistoryVertexState hZ history v).1.2)
      then 1 else 0 := by
  unfold markedMemoryHistoryAddressLineHit
  rw [← markedMemoryHistoryGhostPending_hit_iff hZ history ha]
  split_ifs <;> rfl

theorem markedMemoryHistoryGhostBirth_lineHit (v : Fin (n+1))
    (birth : MarkedMemoryGhostBirthIndex (markedMemoryHistoryVertexGhost hZ history v)) :
    markedMemoryHistoryAddressLineHit hZ history
      (Sum.inr ⟨markedMemoryHistoryGhostTime n v,
        markedMemoryHistoryGhostTraceBirth hZ history v birth⟩) v = 1 := by
  change (if markedMemoryAnchoredPrimeHits
    (markedMemoryHistoryTraceBirthAnchor hZ history (markedMemoryHistoryGhostTime n v)
      (markedMemoryHistoryGhostTraceBirth hZ history v birth))
    (markedMemoryHistoryVertexPositions hZ history v) (markedMemoryHistoryVertexPrimitive hZ history v)
    then (1 : ℝ) else 0) = 1
  rw [markedMemoryHistoryGhostTraceBirth_anchor]
  exact ite_eq_left rfl

/-- An active visit or the actual ghost-birth vertex can provide this
reference anchor; its hit function is exactly the primewise line test. -/
theorem markedMemoryHistoryAddressLineHit_eq_primewise
    (a : MarkedMemoryHistoryTraceAddress hZ history) (p : Nat.Primes) (v₀ : Fin (n+1))
    (ha : markedMemoryHistoryTraceAddressAnchor hZ history a =
      ⟨p, markedMemoryHistoryPrimeLines hZ history p v₀⟩) (v : Fin (n+1)) :
    markedMemoryHistoryAddressLineHit hZ history a v =
      markedLineHit (markedMemoryHistoryPrimeLines hZ history p) v
        (markedMemoryHistoryPrimeLines hZ history p v₀) := by
  unfold markedMemoryHistoryAddressLineHit
  rw [ha]
  rfl

def markedMemoryHistoryGhostLineScalar (qStage : ℕ → ℝ) (j : ℕ)
    (event : MarkedMemoryHistoryGhostScalarEvent hZ history) : ℝ :=
  let e := 1-qStage (j+event.1.val)
  let hit := markedMemoryHistoryAddressLineHit hZ history
    (markedMemoryHistoryGhostScalarOrigin hZ history event) event.1
  match event.2 with
  | Sum.inl old =>
      if old.2 ∈ (markedMemoryHistoryVertexGhost hZ history event.1).deletion old.1
      then -e*hit else 1-e*hit
  | Sum.inr _ => -e*hit

theorem markedMemoryHistoryGhostEventScalar_line
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ history) (qStage : ℕ → ℝ) (j : ℕ)
    (event : MarkedMemoryHistoryGhostScalarEvent hZ history) :
    markedMemoryHistoryGhostEventScalar hZ history qStage j event =
      markedMemoryHistoryGhostLineScalar hZ history qStage j event := by
  rcases event with ⟨v, old | birth⟩
  · rcases old with ⟨band,k⟩
    have hh := markedMemoryHistoryGhostPending_lineHit hZ history ha v band k
    change markedMemoryGhostOldScalar hZ (markedMemoryHistoryVertexState hZ history v)
        (markedMemoryHistoryVertexGhost hZ history v) (qStage (j+v.val)) band k =
      if k ∈ (markedMemoryHistoryVertexGhost hZ history v).deletion band then
        -(1-qStage (j+v.val)) * markedMemoryHistoryAddressLineHit hZ history
          (markedMemoryHistoryGhostSourceOrigin hZ history v (Sum.inr ⟨band,k⟩)) v
      else 1-(1-qStage (j+v.val)) * markedMemoryHistoryAddressLineHit hZ history
          (markedMemoryHistoryGhostSourceOrigin hZ history v (Sum.inr ⟨band,k⟩)) v
    rw [hh]
    unfold markedMemoryGhostOldScalar
    by_cases hd : k ∈ (markedMemoryHistoryVertexGhost hZ history v).deletion band
    · have hk := (markedMemoryHistoryVertexGhost hZ history v).allowed band hd
      simp only [hd, hk, ite_true, mul_one]
    · by_cases hk : k ∈ markedRawGroupHitIndices (markedMemoryHistoryVertexState hZ history v).2.2 band
          (markedMemoryHistoryVertexState hZ history v).1.1
          (hZ _ (markedMemoryHistoryVertexState hZ history v).1.2)
      · simp only [hd, hk, ite_false, ite_true, mul_one]
        ring
      · simp only [hd, hk, ite_false, mul_zero, sub_zero]
  · change -(1-qStage (j+v.val)) = -(1-qStage (j+v.val)) *
      markedMemoryHistoryAddressLineHit hZ history
        (Sum.inr ⟨markedMemoryHistoryGhostTime n v,
          markedMemoryHistoryGhostTraceBirth hZ history v birth⟩) v
    rw [markedMemoryHistoryGhostBirth_lineHit, mul_one]

end
end ArtinMatthews
