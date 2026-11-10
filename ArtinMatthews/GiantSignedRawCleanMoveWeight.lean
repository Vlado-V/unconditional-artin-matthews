module

public import ArtinMatthews.GiantSignedRawCleanChoice
public import ArtinMatthews.GiantSignedRawEdgeSplit
public import ArtinMatthews.GiantSignedCopiedTarget
public import ArtinMatthews.GiantSignedEdgeEmpty
public import ArtinMatthews.GiantSignedRawCleanSplit
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

/-! The original clean move has the literal fresh target mass and
translates the entire pending memory with both original rho factors. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

section FreeLabels
variable {B : Type*} [Fintype B] {PB : B → Finset ℕ}

theorem giantSignedPatternFreeLabels_mass {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (C : B → Finset (Fin k))
    (a : MarkedPhysicalMarking PB (k+ell)) :
    giantSignedFreePrimeMass (fun g p => (ν g p : ℂ)) (giantSignedPatternFreeLabels C a) =
      (idealFreshTargetMass ν C a : ℂ) := by
  have h := giantSignedPatternFill_mass ν C a (giantSignedPatternFreeLabels C a)
  rw [giantSignedPatternFill_freeLabels C a a (fun _ _ _ => rfl)] at h
  exact h

variable [DecidableEq B] {t : B → ℕ}

omit [DecidableEq B] in
theorem giantSignedEdgeMoveCoefficient_emptyChoice
    (ν : ∀ g, PB g → ℂ) (V : B → ℝ) (ρ : ℝ) (Δ : ℤ) (D : ℕ)
    (source target : GiantSignedPrimeTuple PB t) (m : GiantSignedMemory PB) :
    giantSignedEdgeMoveCoefficient ν V ρ Δ D source target m (giantSignedEmptyEdgeChoice m) =
      giantSignedFreePrimeMass ν target *
        ((giantSignedPendingDamping ρ m : ℂ) *
          (giantSignedPendingDamping ρ (giantSignedMemoryTranslate Δ m) : ℂ)) := by
  have hh : GiantSignedEdgeHits Δ m target (giantSignedEmptyEdgeChoice m) ∧
      GiantSignedEdgePromotionBan D (giantSignedEmptyEdgeChoice (t := t) m).2.1 target := by
    constructor <;> intro g i <;> exact Fin.elim0 i
  have ht : giantSignedEdgeTarget Δ m source (giantSignedEmptyEdgeChoice m) =
      giantSignedMemoryTranslate Δ m :=
    giantSignedEdgeTarget_empty Δ m source (giantSignedEmptyEdgeChoice (t := t) m).2.2
  have hp : (∏ g, ∏ i, ν g (giantSignedEdgeSelected (∅ : Finset (Fin (t g)))
      (target g) i)) = 1 := by
    apply Finset.prod_eq_one
    intro g _
    apply Finset.prod_eq_one
    intro i _
    exact (Nat.not_lt_zero _ (by simpa only [Finset.card_empty] using i.isLt)).elim
  have hm := giantSignedSelectedFresh_mass ν (fun _ => ∅) target
  rw [hp, one_mul] at hm
  unfold giantSignedEdgeMoveCoefficient
  rw [ite_eq_left hh, ht]
  change giantSignedPromotionCharge V (fun _ => 0) *
    giantSignedFreshPrimeMass ν (fun _ => ∅) target *
      ((giantSignedPendingDamping ρ m : ℂ) *
        (giantSignedPendingDamping ρ (giantSignedMemoryTranslate Δ m) : ℂ)) = _
  rw [hm]
  simp only [giantSignedPromotionCharge, pow_zero, Finset.prod_const_one, one_mul]

end FreeLabels

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ} {C : B → Finset (Fin k)}

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedRawClean_move_weight
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (κ : ℤ) (ρ : ℝ)
    (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) (hr : GiantSignedRawEdgeClean r) :
    giantSignedEdgeMoveCoefficient (fun g p => (ν g p : ℂ)) V ρ
      (κ * (giantSignedRawEdgeProduct s r : ℤ)) (giantSignedRawEdgeProduct s r)
      (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r))
      (giantSignedPatternFreeLabels C r.bigTarget) s.2.2 r.choice =
    (idealFreshTargetMass ν C r.bigTarget : ℂ) *
      ((giantSignedPendingDamping ρ s.2.2 : ℂ) *
        (giantSignedPendingDamping ρ
          (giantSignedMemoryTranslate (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2) : ℂ)) := by
  have he := (giantSignedEdgeChoiceClean_iff s.2.2 r.choice).mp
    ((giantSignedRawEdgeClean_iff_choiceClean r).mp hr)
  rw [he, giantSignedEdgeMoveCoefficient_emptyChoice, giantSignedPatternFreeLabels_mass]

omit [DecidableEq S] [DecidableEq B] in
theorem giantSignedRawClean_target_memory (κ : ℤ) (s : GiantSignedState PS PB (k+ell))
    (r : GiantSignedRawEdgeMove PS PB ell C s.2.2) (hr : GiantSignedRawEdgeClean r) :
    (giantSignedRawEdgeTarget κ s r).2.2 =
      giantSignedMemoryTranslate (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2 := by
  have he := (giantSignedEdgeChoiceClean_iff s.2.2 r.choice).mp
    ((giantSignedRawEdgeClean_iff_choiceClean r).mp hr)
  change giantSignedEdgeTarget (κ * (giantSignedRawEdgeProduct s r : ℤ)) s.2.2
    (giantSignedPatternFreeLabels C (giantSignedRawEdgeBigSource s r)) r.choice = _
  rw [he]
  exact giantSignedEdgeTarget_empty _ _ _
    (giantSignedEmptyEdgeChoice (t := fun g => ell + (C g).card) s.2.2).2.2

end
end ArtinMatthews
