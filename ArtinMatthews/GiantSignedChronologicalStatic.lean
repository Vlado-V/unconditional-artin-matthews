module

public import ArtinMatthews.GiantSignedChronologicalWeight
public import ArtinMatthews.GiantTwoSidedRootCRTJoin
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

/-! The original combined label data attached to an actual signed chronology.
The small state is transported by the same full dilation as the big memory. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section

variable {S B : Type*} {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
variable {C : Fin n → B → Finset (Fin k)} {batch : Fin (n + 1) → B → ℕ}

def giantSignedChronologicalJoinedPattern (C : Fin n → B → Finset (Fin k))
    (i : Fin n) : S ⊕ B → Finset (Fin k) :=
  Sum.elim (fun _ => ∅) (C i)

variable [Fintype S]

def giantSignedChronologicalJoinedLabels
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (v : Fin (n + 1)) :
    MarkedPhysicalMarking (Sum.elim PS PB) (k + ell) :=
  fun j => match j with
    | .inl s => (h.state v).1.val.2 s
    | .inr b => (h.state v).2.1 b

def giantSignedChronologicalJoinedSourcePermutation
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    S ⊕ B → Equiv.Perm (Fin (k + ell)) :=
  Sum.elim (h.sourceSmallPermutation i) (h.sourceBigPermutation i)

def giantSignedChronologicalJoinedTargetPermutation
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    S ⊕ B → Equiv.Perm (Fin (k + ell)) :=
  Sum.elim (h.targetSmallPermutation i) (h.targetBigPermutation i)

def giantSignedChronologicalJoinedAuxiliary
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    GiantTwoSidedPatternAuxiliary (Sum.elim PS PB)
      (giantSignedChronologicalJoinedPattern (S := S) C i) :=
  fun j => match j with
    | .inl _ => fun a => (Finset.notMem_empty a.val a.property).elim
    | .inr b => h.auxiliary i b

private theorem joinedSmallAuxiliaryProd {R : Type*} [CommMonoid R] (i : Fin n) (s : S)
    (f : ↥(giantSignedChronologicalJoinedPattern C i (.inl s)) → R) :
    (∏ a, f a) = 1 := by
  apply Finset.prod_eq_one
  intro a _
  exact (Finset.notMem_empty a.val a.property).elim

variable [Fintype B]

theorem giantSignedChronologicalJoinedCopiedProduct_eq
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    giantTwoSidedPatternCopiedProduct (giantSignedChronologicalJoinedPattern C i)
      (giantTwoSidedPermuteLabels (giantSignedChronologicalJoinedSourcePermutation h i)
        (giantSignedChronologicalJoinedLabels h i.castSucc)) =
      giantSignedChronologicalSmallProduct h i *
        giantTwoSidedPatternCopiedProduct (C i) (giantSignedChronologicalBigSource h i) := by
  unfold giantTwoSidedPatternCopiedProduct giantSignedChronologicalSmallProduct
  rw [Fintype.prod_sum_type]
  simp only [giantSignedChronologicalJoinedPattern, Sum.elim_inl, Finset.sdiff_empty]
  rfl

theorem giantSignedChronologicalJoinedAuxiliaryProduct_eq
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    giantTwoSidedPatternAuxiliaryProduct (giantSignedChronologicalJoinedAuxiliary h i) =
      giantTwoSidedPatternAuxiliaryProduct (h.auxiliary i) := by
  unfold giantTwoSidedPatternAuxiliaryProduct
  rw [Fintype.prod_sum_type]
  simp only [joinedSmallAuxiliaryProd (C := C) i, Finset.prod_const_one, one_mul]
  rfl

theorem giantSignedChronologicalJoinedAuxiliaryMass_eq
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    giantTwoSidedPatternAuxiliaryMass (giantSignedChronologicalJoinedAuxiliary h i) =
      giantTwoSidedPatternAuxiliaryMass (h.auxiliary i) := by
  unfold giantTwoSidedPatternAuxiliaryMass
  rw [Fintype.prod_sum_type]
  simp only [joinedSmallAuxiliaryProd (C := C) i, Finset.prod_const_one, one_mul]
  rfl

theorem giantSignedChronologicalJoinedDilation_eq
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (i : Fin n) :
    giantTwoSidedPatternDilation (giantSignedChronologicalJoinedPattern C i)
      (giantTwoSidedPermuteLabels (giantSignedChronologicalJoinedSourcePermutation h i)
        (giantSignedChronologicalJoinedLabels h i.castSucc))
      (giantSignedChronologicalJoinedAuxiliary h i) =
        giantSignedChronologicalProduct h i := by
  rw [giantTwoSidedPatternDilation, giantSignedChronologicalJoinedCopiedProduct_eq,
    giantSignedChronologicalJoinedAuxiliaryProduct_eq, giantSignedChronologicalProduct, mul_assoc]

theorem giantTwoSidedResidueSlotNormalization_sum [DecidableEq S] [DecidableEq B] (M : ℕ) :
    giantTwoSidedResidueSlotNormalization (J := S ⊕ B) M =
      giantTwoSidedResidueSlotNormalization (J := S) M *
        giantTwoSidedResidueSlotNormalization (J := B) M := by
  simp only [giantTwoSidedResidueSlotNormalization, Fintype.card_fun, Fintype.card_sum,
    pow_add, Nat.cast_mul, mul_pow, mul_inv]

theorem giantSignedChronologicalJoinedStaticLabels
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    (hc : GiantSignedChronologicalCompatible κ h)
    (hbig : ∀ v, MarkedPhysicalMarkingDistinct (h.state v).2.1) :
    GiantTwoSidedStaticLabels (giantSignedChronologicalJoinedPattern C)
      (giantSignedChronologicalJoinedSourcePermutation h)
      (giantSignedChronologicalJoinedTargetPermutation h)
      (giantSignedChronologicalJoinedAuxiliary h) (giantSignedChronologicalJoinedLabels h) := by
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · intro v j
    cases j with
    | inl s => exact (h.state v).1.property.1 s
    | inr b => exact hbig v b
  · intro j l hl
    cases j with
    | inl s => exact (hc i).1 s l
    | inr b => exact (hc i).2.2.1 b l hl
  · intro g j a l
    cases g with
    | inl s => exact (Finset.notMem_empty a.val a.property).elim
    | inr b =>
      have hban := (hc i).2.2.2.2.2 b a
      cases j with
      | inl s => exact hban.1 s l
      | inr c => exact hban.2 c l

theorem giantSignedChronologicalJoinedIncrement_eq
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ) (i : Fin n) :
    giantTwoSidedLabelIncrement (giantSignedChronologicalJoinedPattern C)
      (giantSignedChronologicalJoinedLabels h) (giantSignedChronologicalJoinedSourcePermutation h)
      (giantSignedChronologicalJoinedAuxiliary h) κ i =
        κ i * (giantSignedChronologicalProduct h i : ℤ) := by
  rw [giantTwoSidedLabelIncrement, giantSignedChronologicalJoinedDilation_eq]

def giantSignedChronologicalJoinedOffset
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ) :
    Fin (n + 1) → ℤ :=
  giantTwoSidedPathOffset
    (giantTwoSidedLabelIncrement (giantSignedChronologicalJoinedPattern C)
      (giantSignedChronologicalJoinedLabels h) (giantSignedChronologicalJoinedSourcePermutation h)
      (giantSignedChronologicalJoinedAuxiliary h) κ)

theorem giantSignedChronologicalSmallResidue_eq_translate
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    (hc : GiantSignedChronologicalCompatible κ h) (v : Fin (n + 1)) :
    (h.state v).1.val.1 =
      giantTwoSidedResidueTranslate (giantSignedChronologicalJoinedOffset h κ v) (h.state 0).1.val.1 := by
  unfold giantSignedChronologicalJoinedOffset
  refine Fin.induction ?_ ?_ v
  · rw [giantTwoSidedPathOffset_zero, giantTwoSidedResidueTranslate_zero]
  · intro i ih
    have hs := (hc i).2.1
    change (h.state i.succ).1.val.1 = giantTwoSidedResidueTranslate
      (κ i * (giantSignedChronologicalProduct h i : ℤ)) (h.state i.castSucc).1.val.1 at hs
    rw [hs, ih, giantTwoSidedPathOffset_succ, giantTwoSidedResidueTranslate_add,
      giantSignedChronologicalJoinedIncrement_eq]

theorem giantSignedChronologicalSmallActive_hit
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    (hc : GiantSignedChronologicalCompatible κ h) (v : Fin (n + 1))
    (p : ↥(markedPhysicalBandPrimes PS))
    (hp : p.val ∈ markedPhysicalActivePrimes (h.state v).1.val.2) :
    (h.state 0).1.val.1 p + (giantSignedChronologicalJoinedOffset h κ v : ZMod p.val) = 0 := by
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hj
  have hindex : giantTwoSidedResidueIndex j ((h.state v).1.val.2 j l) = p :=
    Subtype.ext hl
  have hz : (h.state v).1.val.1 p = 0 :=
    (congrArg (fun index : ↥(markedPhysicalBandPrimes PS) =>
      (h.state v).1.val.1 index = 0) hindex).mp ((h.state v).1.property.2 j l)
  rw [giantSignedChronologicalSmallResidue_eq_translate h κ hc v] at hz
  exact hz

theorem giantSignedChronologicalSmallActiveCompatible
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)
    (hc : GiantSignedChronologicalCompatible κ h) :
    GiantTwoSidedActiveCompatible Finset.univ (fun v => (h.state v).1.val.2)
      (giantSignedChronologicalJoinedOffset h κ) := by
  let labels := fun v : Fin (n + 1) => (h.state v).1.val.2
  change GiantTwoSidedActiveCompatible Finset.univ labels (giantSignedChronologicalJoinedOffset h κ)
  intro p v _ hp
  let pBand : ↥(markedPhysicalBandPrimes PS) :=
    ⟨p.val, markedPhysicalPathUsedPrimes_subset Finset.univ labels p.property⟩
  have hv := giantSignedChronologicalSmallActive_hit h κ hc v pBand hp
  have hfirst := giantSignedChronologicalSmallActive_hit h κ hc
    (giantTwoSidedActiveVisit Finset.univ labels p).val pBand
    (giantTwoSidedActiveVisit_mem Finset.univ labels p)
  exact add_left_cancel (hv.trans hfirst.symm)

end

end ArtinMatthews
