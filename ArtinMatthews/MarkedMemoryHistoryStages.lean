module

public import ArtinMatthews.MarkedMemoryHistoryBirths
public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotOrigins
public import ArtinMatthews.MarkedMemoryHistoryGhostOrigins
public import ArtinMatthews.MarkedMemoryHistoryOriginComposition
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

/-! Every literal intermediate population in chronological order: before
and after each ghost, with the next history starting after the edge. -/
namespace ArtinMatthews
noncomputable section

def MarkedMemoryHistoryStage : ℕ → Type
  | 0 => Bool
  | n+1 => Unit ⊕ (Unit ⊕ MarkedMemoryHistoryStage n)

def markedMemoryHistoryStageTime : {n : ℕ} → MarkedMemoryHistoryStage n → ℕ
  | 0,false => 0
  | 0,true => 1
  | _+1,Sum.inl _ => 0
  | _+1,Sum.inr (Sum.inl _) => 1
  | _+1,Sum.inr (Sum.inr t) => markedMemoryHistoryStageTime t+2

def markedMemoryHistoryStageState {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → MarkedMemoryHistoryStage n → MarkedRawState P (pads+1) B Z
  | 0,s,_,false => s
  | 0,s,ghost,true => markedMemoryGhostChoiceTarget hZ s ghost
  | _+1,s,_,Sum.inl _ => s
  | _+1,s,history,Sum.inr (Sum.inl _) => markedMemoryGhostChoiceTarget hZ s history.1
  | _+1,_,history,Sum.inr (Sum.inr t) => markedMemoryHistoryStageState hZ history.2.2 t

/-- Every intermediate particle has its literal old-or-birth history identity. -/
def markedMemoryHistoryStageOrigin {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) → (t : MarkedMemoryHistoryStage n) →
      MarkedMemoryPopulationIndex (markedMemoryHistoryStageState hZ history t) ↪
        (MarkedMemoryPopulationIndex s ⊕ MarkedMemoryHistoryBirths hZ history)
  | 0,_,_,false => Function.Embedding.inl
  | 0,s,ghost,true => markedMemoryGhostPopulationOrigin hZ s ghost
  | _+1,_,_,Sum.inl _ => Function.Embedding.inl
  | _+1,s,history,Sum.inr (Sum.inl _) =>
      (markedMemoryGhostPopulationOrigin hZ s history.1).trans
        (Function.Embedding.sumMap (Function.Embedding.refl _) Function.Embedding.inl)
  | _+1,s,history,Sum.inr (Sum.inr t) =>
      markedMemoryOriginCompose
        (markedMemoryOriginCompose (markedMemoryHistoryStageOrigin hZ history.2.2 t)
          (markedMemoryEdgeSlotPopulationOrigin hZ
            (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1))
        (markedMemoryGhostPopulationOrigin hZ s history.1)

/-- The actual mark follows the history identity at every intermediate stage. -/
theorem markedMemoryHistoryStageOrigin_prime {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (t : MarkedMemoryHistoryStage n)
    (i : MarkedMemoryPopulationIndex (markedMemoryHistoryStageState hZ history t)) :
    Sum.elim (markedMemoryPopulationPrime s) (markedMemoryHistoryBirthPrime hZ history)
      (markedMemoryHistoryStageOrigin hZ history t i) =
        markedMemoryPopulationPrime (markedMemoryHistoryStageState hZ history t) i := by
  induction n generalizing s with
  | zero =>
    cases t with
    | false => rfl
    | true => exact markedMemoryGhostPopulationOrigin_prime hZ s history i
  | succ n ih =>
    rcases t with before | after | tail
    · rfl
    · have h := markedMemoryGhostPopulationOrigin_prime hZ s history.1 i
      change Sum.elim _ (Sum.elim _ (Sum.elim _ _))
        (Sum.map id Sum.inl (markedMemoryGhostPopulationOrigin hZ s history.1 i)) = _
      generalize ho : markedMemoryGhostPopulationOrigin hZ s history.1 i = o at h ⊢
      cases o <;> exact h
    · exact markedMemoryOriginCompose_mark _ _ _ _ _ _ _
        (markedMemoryOriginCompose_mark _ _ _ _ _ _ _
          (ih history.2.2 tail) (markedMemoryEdgeSlotPopulationOrigin_prime hZ _ history.2.1))
        (markedMemoryGhostPopulationOrigin_prime hZ s history.1) i

/-- Actual stage addresses have their chronological index, without collisions. -/
theorem markedMemoryHistoryStageTime_injective (n : ℕ) :
    Function.Injective (@markedMemoryHistoryStageTime n) := by
  induction n with
  | zero =>
    intro a b h
    cases a <;> cases b
    all_goals first | rfl | simp [markedMemoryHistoryStageTime] at h
  | succ n ih =>
    intro a b h
    rcases a with a | a | a <;> rcases b with b | b | b
    all_goals simp only [markedMemoryHistoryStageTime] at h
    all_goals first | omega | (congr 2; exact ih (by omega)) | rfl

end
end ArtinMatthews
