module

public import ArtinMatthews.GiantSignedLifespanMemorySchedule
public import ArtinMatthews.GiantSignedChronologicalStatic
public import ArtinMatthews.GiantFullPrimeMean
public import ArtinMatthews.GiantSignedLifespanPathSlots
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

/-! The original copied-slot geometry supplies the ordered memory schedule
for fixed labels and a supported lifespan choice. -/

namespace ArtinMatthews
open Finset
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)}

local notation "JoinedBands" => Sum.elim PS PB
local notation "Joined" => giantSignedChronologicalJoinedPattern (S := S) C

def giantSignedLifespanPathSchedule
    (labels : Fin (n+1) → MarkedPhysicalMarking JoinedBands (k+ell))
    (π τ : Fin n → S ⊕ B → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i, GiantTwoSidedPatternAuxiliary JoinedBands (Joined i)) (κ : Fin n → ℤ)
    (hP : ∀ (g : S ⊕ B) (p : ℕ), p ∈ JoinedBands g → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (JoinedBands i) (JoinedBands j)))
    (hκ : ∀ i, 0 < (κ i).natAbs) (hsize : ∀ i g p, p ∈ JoinedBands g → (κ i).natAbs < p)
    (hguard : GiantTwoSidedStaticLabels (ell := ell) Joined π τ aux labels)
    (hcompat : GiantTwoSidedActiveCompatible univ labels
      (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement (ell := ell) Joined labels π aux κ)))
    (q : Fin (n+1) → ℝ) (c : ∀ (g : B) (p : PB g),
      GiantSignedResidueLifespanChoice (giantSignedActualActiveVisits labels p.val))
    (hw : ∀ (g : B) (p : PB g), giantSignedResidueLifespanWeight p.val
      (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement (ell := ell) Joined labels π aux κ)) q
      (giantSignedActualActiveVisits labels p.val) (c g p) ≠ 0)
    (order : ∀ (v : Fin (n+1)) (g : B), Fin (giantSignedGhostVisitBorn (c g) v).card ≃
      ↥(giantSignedGhostVisitBorn (c g) v)) :
    GiantSignedLifespanScheduleData (P := PB) (A := fun _g p => giantSignedActualActiveVisits labels p.val)
      c (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement (ell := ell) Joined labels π aux κ)) q
      (fun i g => ell+(C i g).card) := by
  let increment := giantTwoSidedLabelIncrement (ell := ell) Joined labels π aux κ
  let source (i : Fin n) : GiantSignedPrimeTuple PB (fun g => ell+(C i g).card) :=
    giantSignedPatternFreeLabels (C i)
    (fun g => giantTwoSidedPermuteLabels (π i) (labels i.castSucc) (Sum.inr g))
  let target (i : Fin n) : GiantSignedPrimeTuple PB (fun g => ell+(C i g).card) :=
    giantSignedPatternFreeLabels (C i)
    (fun g => giantTwoSidedPermuteLabels (τ i) (labels i.succ) (Sum.inr g))
  refine ⟨increment,giantTwoSidedPathOffset_succ increment,source,target,?_,?_,?_,?_,hw,order⟩
  · intro i g
    exact giantSignedPatternFreeLabels_injective (C i) _
      (fun g => (hguard.1 i.castSucc (Sum.inr g)).comp (π i (Sum.inr g)).injective) g
  · intro i g
    exact giantSignedPatternFreeLabels_injective (C i) _
      (fun g => (hguard.1 i.succ (Sum.inr g)).comp (τ i (Sum.inr g)).injective) g
  · intro i g p ha hb
    exact ((giantSignedLifespanPath_free_slots hP hdis hκ hsize hguard hcompat i (Sum.inr g) p).1).mpr ⟨ha,hb⟩
  · intro i g p ha hb
    exact ((giantSignedLifespanPath_free_slots hP hdis hκ hsize hguard hcompat i (Sum.inr g) p).2).mpr ⟨ha,hb⟩

end
end ArtinMatthews
