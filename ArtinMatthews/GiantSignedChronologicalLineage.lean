module

public import ArtinMatthews.GiantSignedBirthLineage
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

/-! Chronological ancestry starts at the empty-memory boundary and uses
the actual visit and raw-edge index maps. The resulting finite support
for distinct births is a consequence of the unbounded dynamics. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch)

def giantSignedChronologicalInitialBirth (g : B) :
    Fin (k+ell) ↪ GiantSignedPerformedBirth (giantSignedChronologicalBirthData h) :=
  ⟨fun i => .inl (g,i), fun _ _ hi => congrArg Prod.snd (Sum.inl.inj hi)⟩

def giantSignedChronologicalVisitBirth (i : Fin (n+1)) (g : B) :
    Fin (batch i g) ↪ GiantSignedPerformedBirth (giantSignedChronologicalBirthData h) where
  toFun z := .inr (.inr ⟨i,g,z⟩)
  inj' := by
    intro z w he
    exact (Function.Embedding.sigmaMk g).injective
      ((Function.Embedding.sigmaMk i).injective (Sum.inr.inj (Sum.inr.inj he)))

def giantSignedChronologicalEdgeBirth (i : Fin n) (g : B) :
    {z : Fin (ell+(C i g).card) // z ∉ (h.edge i).2.1 g} ↪
      GiantSignedPerformedBirth (giantSignedChronologicalBirthData h) where
  toFun z := .inr (.inl ⟨i,g,z⟩)
  inj' := by
    intro z w he
    exact (Function.Embedding.sigmaMk g).injective
      ((Function.Embedding.sigmaMk i).injective (Sum.inl.inj (Sum.inr.inj he)))

def giantSignedChronologicalInitialLineage (hb : GiantSignedChronologicalBoundary h) (g : B) :
    GiantSignedBirthLineage (giantSignedChronologicalBirthData h) (h.state 0) g 0 := by
  have hz : (h.state 0).2.2.1 g = 0 := congrArg (fun m : GiantSignedMemory PB => m.1 g) hb.1
  letI : IsEmpty (Fin ((h.state 0).2.2.1 g)) := ⟨fun z => by
    have hlt := z.isLt
    omega⟩
  refine ⟨(Equiv.sumEmpty _ _).toEmbedding.trans (giantSignedChronologicalInitialBirth h g), ?_, ?_⟩
  · rintro (i | i)
    · exact le_rfl
    · exact isEmptyElim i
  · rintro (i | i)
    · rfl
    · exact isEmptyElim i

def giantSignedChronologicalVisitLineage (i : Fin (n+1)) (g : B)
    (l : GiantSignedBirthLineage (giantSignedChronologicalBirthData h) (h.state i) g (2*i.val)) :
    GiantSignedBirthLineage (giantSignedChronologicalBirthData h)
      (giantSignedChronologicalAfterVisitState h i) g (2*i.val+1) := by
  refine giantSignedBirthLineage_extend l (giantSignedChronologicalVisitOrigin h i g)
    (giantSignedChronologicalVisitBirth h i g) (by omega) ?_ ?_ ?_
  · intro z
    change 2*i.val < 2*i.val+1
    omega
  · intro z
    exact le_rfl
  · intro z
    rw [giantSignedChronologicalVisitOrigin_prime h i g z]
    rcases giantSignedChronologicalVisitOrigin h i g z with u | u <;> rfl

def giantSignedChronologicalNextLineage (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (i : Fin n) (g : B)
    (l : GiantSignedBirthLineage (giantSignedChronologicalBirthData h)
      (giantSignedChronologicalAfterVisitState h i.castSucc) g (2*i.castSucc.val+1)) :
    GiantSignedBirthLineage (giantSignedChronologicalBirthData h) (h.state i.succ) g (2*i.succ.val) := by
  refine giantSignedBirthLineage_extend l (giantSignedChronologicalEdgeOrigin κ h ha.compatible i g)
    (giantSignedChronologicalEdgeBirth h i g) ?_ ?_ ?_ ?_
  · change 2*i.val+1 ≤ 2*(i.val+1)
    omega
  · intro z
    change 2*i.val+1 < 2*i.val+2
    omega
  · intro z
    change 2*i.val+2 ≤ 2*(i.val+1)
    omega
  · intro z
    rw [giantSignedChronologicalEdgeOrigin_prime κ h ha i g z]
    rcases giantSignedChronologicalEdgeOrigin κ h ha.compatible i g z with u | u <;> rfl

def giantSignedChronologicalPreLineage (κ : Fin n → ℤ) (ha : GiantSignedChronologicalAdmissible κ h)
    (i : Fin (n+1)) (g : B) :
    GiantSignedBirthLineage (giantSignedChronologicalBirthData h) (h.state i) g (2*i.val) := by
  induction i using Fin.induction with
  | zero => exact giantSignedChronologicalInitialLineage h ha.boundary g
  | succ i ih =>
      exact giantSignedChronologicalNextLineage h κ ha i g
        (giantSignedChronologicalVisitLineage h i.castSucc g ih)

theorem giantSignedChronological_distinct_degrees (κ : Fin n → ℤ)
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h)) (i : Fin (n+1)) (g : B) :
    k+ell+(h.state i).2.2.1 g ≤ (PB g).card ∧
      k+ell+(giantSignedChronologicalGhostTarget h i).1 g ≤ (PB g).card ∧
      batch i g ≤ (PB g).card := by
  let pre := giantSignedChronologicalPreLineage h κ ha i g
  have hp := giantSignedBirthLineage_card_le pre hd
  have hv := giantSignedBirthLineage_card_le (giantSignedChronologicalVisitLineage h i g pre) hd
  refine ⟨hp, hv, ?_⟩
  change k+ell+(giantSignedFixedGhostTarget (h.state i).2.2 (batch i) (h.deleted i) (h.born i)).1 g
      ≤ (PB g).card at hv
  rw [giantSignedFixedGhostTarget_degree] at hv
  omega

end
end ArtinMatthews
