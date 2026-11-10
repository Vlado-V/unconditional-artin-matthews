module

public import ArtinMatthews.MarkedMemoryHistoryPrimeWeight
public import ArtinMatthews.MarkedMemoryHistoryEdgeDeaths
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

/-! Each promotion charge is located on its actual old pending identity.
The target is the actual new active slot after both slot permutations.
Its source and target lie on the same computed indexed lifespan. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryEdgePromotionSlot {s : MarkedRawState P (pads+1) B Z}
    (edge : MarkedMemoryEdgeChoice hZ s) (r : MarkedMemoryEdgePromotionIndex hZ edge) :
    Fin (s.2.2.1.1 r.1 : ℕ) :=
  Classical.choose (Option.ne_none_iff_exists'.mp r.2)

theorem markedMemoryEdgePromotionSlot_spec {s : MarkedRawState P (pads+1) B Z}
    (edge : MarkedMemoryEdgeChoice hZ s) (r : MarkedMemoryEdgePromotionIndex hZ edge) :
    edge.2.1.promotions r.1 = some (markedMemoryEdgePromotionSlot hZ edge r) :=
  Classical.choose_spec (Option.ne_none_iff_exists'.mp r.2)

theorem markedMemoryEdgeSlotOrigin_promoted {s : MarkedRawState P (pads+1) B Z}
    (edge : MarkedMemoryEdgeChoice hZ s) (r : MarkedMemoryEdgePromotionIndex hZ edge) :
    markedMemoryEdgeSlotPopulationOrigin hZ s edge
      (Sum.inl ⟨r.1,(edge.2.2 r.1).symm (Fin.last pads)⟩) =
        Sum.inl (Sum.inr ⟨r.1,markedMemoryEdgePromotionSlot hZ edge r⟩) := by
  change Sum.map (markedMemorySlotPopulationEquiv edge.1 s) id
    (markedMemoryEdgePopulationOrigin hZ (markedRawSlotEquiv edge.1 s) edge.2.1
      (Sum.inl ⟨r.1,edge.2.2 r.1 ((edge.2.2 r.1).symm (Fin.last pads))⟩)) = _
  rw [Equiv.apply_symm_apply, markedMemoryEdgePopulationOrigin_last_some hZ
    (markedRawSlotEquiv edge.1 s) edge.2.1 r.1 (markedMemoryEdgePromotionSlot hZ edge r)
    (markedMemoryEdgePromotionSlot_spec hZ edge r)]
  rfl

def markedMemoryHistoryPromotionTime :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
        MarkedMemoryHistoryPromotionIndex hZ history → ℕ
  | 0,_,_ => PEmpty.elim
  | _+1,_,history => Sum.elim (fun _ => 1)
      (fun r => markedMemoryHistoryPromotionTime history.2.2 r + 2)

def markedMemoryHistoryPromotionSource :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
      (r : MarkedMemoryHistoryPromotionIndex hZ history) →
      MarkedMemoryHistoryTracePopulation hZ history (markedMemoryHistoryPromotionTime hZ history r)
  | 0,_,_,r => PEmpty.elim r
  | _+1,_,history,Sum.inl r =>
      Sum.inr ⟨r.1,markedMemoryEdgePromotionSlot hZ history.2.1 r⟩
  | _+1,_,history,Sum.inr r => markedMemoryHistoryPromotionSource history.2.2 r

def markedMemoryHistoryPromotionTarget :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
      (r : MarkedMemoryHistoryPromotionIndex hZ history) →
      MarkedMemoryHistoryTracePopulation hZ history (markedMemoryHistoryPromotionTime hZ history r+1)
  | 0,_,_,r => PEmpty.elim r
  | _+1,_,history,Sum.inl r => Sum.inl ⟨r.1,(history.2.1.2.2 r.1).symm (Fin.last pads)⟩
  | _+1,_,history,Sum.inr r => markedMemoryHistoryPromotionTarget history.2.2 r

def markedMemoryHistoryPromotionOrigin {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (r : MarkedMemoryHistoryPromotionIndex hZ history) : MarkedMemoryHistoryTraceAddress hZ history :=
  markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
    (markedMemoryHistoryPromotionTime hZ history r) (markedMemoryHistoryPromotionSource hZ history r)

theorem markedMemoryHistoryPromotionTime_lt {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryHistoryPromotionTime hZ history r < 2*n+1 := by
  induction n generalizing s with
  | zero => exact PEmpty.elim r
  | succ n ih =>
    cases r with
    | inl r => change 1 < 2*(n+1)+1; omega
    | inr r =>
      have ht := ih history.2.2 r
      change markedMemoryHistoryPromotionTime hZ history.2.2 r+2 < 2*(n+1)+1
      omega

theorem markedMemoryHistoryPromotionTime_odd {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryHistoryPromotionTime hZ history r % 2 = 1 := by
  induction n generalizing s with
  | zero => exact PEmpty.elim r
  | succ n ih =>
    cases r with
    | inl r => rfl
    | inr r =>
      have ht := ih history.2.2 r
      change (markedMemoryHistoryPromotionTime hZ history.2.2 r+2) % 2 = 1
      omega

theorem markedMemoryHistoryPromotion_transition {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryHistoryTraceStep hZ history (markedMemoryHistoryPromotionTime hZ history r)
      (markedMemoryHistoryPromotionTarget hZ history r) =
        Sum.inl (markedMemoryHistoryPromotionSource hZ history r) := by
  induction n generalizing s with
  | zero => exact PEmpty.elim r
  | succ n ih =>
    cases r with
    | inl r => exact markedMemoryEdgeSlotOrigin_promoted hZ history.2.1 r
    | inr r => exact ih history.2.2 r

/-- The actual target active index carries the same old lifespan address. -/
theorem markedMemoryHistoryPromotion_target_origin {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryLineageOrigin (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history)
      (markedMemoryHistoryPromotionTime hZ history r+1) (markedMemoryHistoryPromotionTarget hZ history r) =
        markedMemoryHistoryPromotionOrigin hZ history r := by
  change Sum.elim _ _ (markedMemoryHistoryTraceStep hZ history _ _) = _
  rw [markedMemoryHistoryPromotion_transition]
  rfl

/-- Both ends of an actual promotion are within the computed lifespan;
its V inverse charge is therefore attached to a surviving old identity. -/
theorem markedMemoryHistoryPromotion_lifespan {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryLineageBirthTime (markedMemoryHistoryPromotionOrigin hZ history r) ≤
        markedMemoryHistoryPromotionTime hZ history r ∧
      markedMemoryHistoryPromotionTime hZ history r+1 ≤
        markedMemoryHistoryLifespanLast hZ history (markedMemoryHistoryPromotionOrigin hZ history r) := by
  have ht := markedMemoryHistoryPromotionTime_lt hZ history r
  have hs := (markedMemoryHistory_lifespan_exact hZ history
    (markedMemoryHistoryPromotionOrigin hZ history r) (markedMemoryHistoryPromotionTime hZ history r)).mp
      ⟨Nat.le_of_lt ht, markedMemoryHistoryPromotionSource hZ history r, rfl⟩
  have hd := (markedMemoryHistory_lifespan_exact hZ history
    (markedMemoryHistoryPromotionOrigin hZ history r) (markedMemoryHistoryPromotionTime hZ history r+1)).mp
      ⟨by omega, markedMemoryHistoryPromotionTarget hZ history r,
        markedMemoryHistoryPromotion_target_origin hZ history r⟩
  exact ⟨hs.1,hd.2⟩

end
end ArtinMatthews
