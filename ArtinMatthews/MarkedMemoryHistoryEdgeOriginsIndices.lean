module

public import Mathlib.Data.Finset.Option
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Injective indexed bookkeeping for one store/promote edge. No numeric particle values occur. -/
namespace ArtinMatthews
noncomputable section

/-- The copied slot, target last slot, surviving old memory, and appended store have their
literal old-or-fresh identities. The only possible store slot is kept distinct from copied slots. -/
def markedMemoryEdgeSplitOriginFn {pads k b : ℕ} (prom : Option (Fin k)) :
    ((Fin pads ⊕ Fin 1) ⊕ ({i : Fin k // i ∉ prom.toFinset} ⊕ Fin b)) →
      (((Fin pads ⊕ Fin 1) ⊕ Fin k) ⊕ PLift (prom = none))
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (Sum.inl i))
  | Sum.inl (Sum.inr _) => match prom with
      | none => Sum.inr ⟨rfl⟩
      | some i => Sum.inl (Sum.inr i)
  | Sum.inr (Sum.inl i) => Sum.inl (Sum.inr i.1)
  | Sum.inr (Sum.inr _) => Sum.inl (Sum.inl (Sum.inr 0))

/-- Each target identity has a different old-or-fresh origin. Old promotions are removed from
survivors, and an appended store is the old last active slot rather than a fresh identity. -/
theorem markedMemoryEdgeSplitOriginFn_injective {pads k b : ℕ}
    (prom : Option (Fin k)) (hb : b ≤ 1) :
    Function.Injective (markedMemoryEdgeSplitOriginFn (pads := pads) (b := b) prom) := by
  let : Subsingleton (Fin b) := (Fin.subsingleton_iff_le_one).mpr hb
  cases prom with
  | none =>
    rintro (a | a) (c | c) h <;> rcases a with (a | a) <;> rcases c with (c | c)
    all_goals simp_all [markedMemoryEdgeSplitOriginFn]
    all_goals first
      | exact Subsingleton.elim _ _
      | exact congrArg Sum.inl (Subtype.ext h)
  | some q =>
    rintro (a | a) (c | c) h <;> rcases a with (a | a) <;> rcases c with (c | c)
    all_goals simp_all [markedMemoryEdgeSplitOriginFn]
    all_goals first
      | exact Subsingleton.elim _ _
      | exact congrArg Sum.inl (Subtype.ext h)
      | exact c.property (by simp [h])
      | exact a.property (by simp [h])

def markedMemoryEdgeSplitOrigin {pads k b : ℕ} (prom : Option (Fin k)) (hb : b ≤ 1) :
    ((Fin pads ⊕ Fin 1) ⊕ ({i : Fin k // i ∉ prom.toFinset} ⊕ Fin b)) ↪
      (((Fin pads ⊕ Fin 1) ⊕ Fin k) ⊕ PLift (prom = none)) :=
  ⟨markedMemoryEdgeSplitOriginFn prom, markedMemoryEdgeSplitOriginFn_injective prom hb⟩

@[simp] theorem markedMemoryEdgeSplitOriginFn_copied {pads k b : ℕ}
    (prom : Option (Fin k)) (i : Fin pads) :
    markedMemoryEdgeSplitOriginFn (b := b) prom (Sum.inl (Sum.inl i)) =
      Sum.inl (Sum.inl (Sum.inl i)) := rfl

@[simp] theorem markedMemoryEdgeSplitOriginFn_survivor {pads k b : ℕ}
    (prom : Option (Fin k)) (i : {i : Fin k // i ∉ prom.toFinset}) :
    markedMemoryEdgeSplitOriginFn (pads := pads) (b := b) prom (Sum.inr (Sum.inl i)) =
      Sum.inl (Sum.inr i.1) := rfl

@[simp] theorem markedMemoryEdgeSplitOriginFn_store {pads k b : ℕ}
    (prom : Option (Fin k)) (i : Fin b) :
    markedMemoryEdgeSplitOriginFn (pads := pads) prom (Sum.inr (Sum.inr i)) =
      Sum.inl (Sum.inl (Sum.inr 0)) := rfl

@[simp] theorem markedMemoryEdgeSplitOriginFn_none {pads k b : ℕ}
    (prom : Option (Fin k)) (hn : prom = none) (i : Fin 1) :
    markedMemoryEdgeSplitOriginFn (pads := pads) (b := b) prom (Sum.inl (Sum.inr i)) =
      Sum.inr ⟨hn⟩ := by subst prom; rfl

@[simp] theorem markedMemoryEdgeSplitOriginFn_some {pads k b : ℕ}
    (prom : Option (Fin k)) (q : Fin k) (hq : prom = some q) (i : Fin 1) :
    markedMemoryEdgeSplitOriginFn (pads := pads) (b := b) prom (Sum.inl (Sum.inr i)) =
      Sum.inl (Sum.inr q) := by subst prom; rfl

end
end ArtinMatthews
