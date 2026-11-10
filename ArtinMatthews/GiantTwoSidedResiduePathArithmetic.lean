module

public import ArtinMatthews.GiantTwoSidedRootCRTJoin
public import ArtinMatthews.GiantFullPrimeMean
public import ArtinMatthews.GiantTwoSidedPatternCompletions
public import ArtinMatthews.GiantTwoSidedResidueEdgeArithmetic
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The original fixed-choice residue path has exactly its prescribed
copied labels at adjacent active visits. Its free slots avoid the dilation. -/

namespace ArtinMatthews
open Finset
noncomputable section

theorem giantTwoSidedPermuteLabels_labelSet {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (π : J → Equiv.Perm (Fin M)) (a : MarkedPhysicalMarking P M) (j : J) :
    markedPhysicalLabelSet (giantTwoSidedPermuteLabels π a) j = markedPhysicalLabelSet a j := by
  ext p
  simp only [markedPhysicalLabelSet, mem_image, mem_univ, true_and, giantTwoSidedPermuteLabels]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨π j i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨(π j).symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell n : ℕ}
variable {C : Fin n → J → Finset (Fin k)}
variable {labels : Fin (n + 1) → MarkedPhysicalMarking P (k + ell)}
variable {π τ : Fin n → J → Equiv.Perm (Fin (k + ell))}
variable {aux : ∀ i, GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin n → ℤ}

/-- Adjacent active labels of the actual residue path are precisely the
copied values in its original source permutation. -/
theorem giantTwoSidedIndependentPath_common_labels
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hstep : ∀ i, 0 < (step i).natAbs) (hsize : ∀ i j p, p ∈ P j → (step i).natAbs < p)
    (hguard : GiantTwoSidedStaticLabels C π τ aux labels)
    (hcompat : GiantTwoSidedActiveCompatible univ labels
      (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)))
    (i : Fin n) (j : J) :
    markedPhysicalLabelSet (labels i.castSucc) j ∩ markedPhysicalLabelSet (labels i.succ) j =
      giantTwoSidedPatternCopiedValues (P j) (C i j)
        (giantTwoSidedPermuteLabels (π i) (labels i.castSucc) j) := by
  let s := giantTwoSidedPermuteLabels (π i) (labels i.castSucc)
  let t := giantTwoSidedPermuteLabels (τ i) (labels i.succ)
  let offset := giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)
  have hshift : offset i.succ = offset i.castSucc +
      step i * (giantTwoSidedPatternDilation (C i) s (aux i) : ℤ) :=
    giantTwoSidedPathOffset_succ (giantTwoSidedLabelIncrement C labels π aux step) i
  have hcongr (p : ℕ) (hs : p ∈ markedPhysicalLabelSet s j)
      (ht : p ∈ markedPhysicalLabelSet t j) :
      (offset i.succ : ZMod p) = (offset i.castSucc : ZMod p) := by
    have hs' : p ∈ markedPhysicalActivePrimes (labels i.castSucc) :=
      mem_biUnion.mpr ⟨j, mem_univ _, by simpa only [s, giantTwoSidedPermuteLabels_labelSet] using hs⟩
    have ht' : p ∈ markedPhysicalActivePrimes (labels i.succ) :=
      mem_biUnion.mpr ⟨j, mem_univ _, by simpa only [t, giantTwoSidedPermuteLabels_labelSet] using ht⟩
    let p' : ↥(markedPhysicalPathUsedPrimes univ labels) :=
      ⟨p, mem_biUnion.mpr ⟨i.castSucc, mem_univ _, hs'⟩⟩
    exact (hcompat p' i.succ (mem_univ _) ht').trans (hcompat p' i.castSucc (mem_univ _) hs').symm
  simpa only [s, t, giantTwoSidedPermuteLabels_labelSet] using
    giantTwoSidedLabelCommon_eq_copied hP hdis (hguard.2 i) (hstep i) (hsize i) hshift j hcongr

/-- The active-visit set used by the lifespan expansion has the same
adjacent common primes as the original copied slots. -/
theorem giantTwoSidedIndependentPath_adjacent_active_iff_copied
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hstep : ∀ i, 0 < (step i).natAbs) (hsize : ∀ i j p, p ∈ P j → (step i).natAbs < p)
    (hguard : GiantTwoSidedStaticLabels C π τ aux labels)
    (hcompat : GiantTwoSidedActiveCompatible univ labels
      (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)))
    (i : Fin n) (j : J) {p : ℕ} (hp : p ∈ P j) :
    i.castSucc ∈ giantSignedActualActiveVisits labels p ∧
      i.succ ∈ giantSignedActualActiveVisits labels p ↔
      p ∈ giantTwoSidedPatternCopiedValues (P j) (C i j)
        (giantTwoSidedPermuteLabels (π i) (labels i.castSucc) j) := by
  have hmem (v : Fin (n + 1)) : v ∈ giantSignedActualActiveVisits labels p ↔
      p ∈ markedPhysicalLabelSet (labels v) j := by
    simpa [giantSignedActualActiveVisits] using markedPhysicalActivePrimes_mem_group hdis (labels v) j hp
  rw [hmem i.castSucc, hmem i.succ, ← mem_inter,
    giantTwoSidedIndependentPath_common_labels hP hdis hstep hsize hguard hcompat i j]

/-- A common active prime has an actual prescribed shared slot and the
same value at both permuted endpoints. -/
theorem giantTwoSidedIndependentPath_adjacent_active_iff_sharedSlot
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hstep : ∀ i, 0 < (step i).natAbs) (hsize : ∀ i j p, p ∈ P j → (step i).natAbs < p)
    (hguard : GiantTwoSidedStaticLabels C π τ aux labels)
    (hcompat : GiantTwoSidedActiveCompatible univ labels
      (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)))
    (i : Fin n) (j : J) {p : ℕ} (hp : p ∈ P j) :
    i.castSucc ∈ giantSignedActualActiveVisits labels p ∧
      i.succ ∈ giantSignedActualActiveVisits labels p ↔
      ∃ l : Fin k, l ∉ C i j ∧
        (giantTwoSidedPermuteLabels (π i) (labels i.castSucc) j (Fin.castAdd ell l)).val = p ∧
        (giantTwoSidedPermuteLabels (τ i) (labels i.succ) j (Fin.castAdd ell l)).val = p := by
  rw [giantTwoSidedIndependentPath_adjacent_active_iff_copied hP hdis hstep hsize hguard hcompat i j hp]
  constructor
  · intro h
    obtain ⟨l, hl, he⟩ := mem_image.mp h
    have hnot := (mem_sdiff.mp hl).2
    exact ⟨l, hnot, he, (congrArg Subtype.val ((hguard.2 i).copied j l hnot)).trans he⟩
  · rintro ⟨l, hl, he, _⟩
    exact mem_image.mpr ⟨l, mem_sdiff.mpr ⟨mem_univ _, hl⟩, he⟩

/-- Each original unshared source and target slot is prime to the
complete dilation at that edge. -/
theorem giantTwoSidedIndependentPath_free_not_dvd
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hguard : GiantTwoSidedStaticLabels C π τ aux labels)
    (i : Fin n) (j : J) (l : GiantTwoSidedPatternFreeSlots (C i j) ell) :
    let s := giantTwoSidedPermuteLabels (π i) (labels i.castSucc)
    let t := giantTwoSidedPermuteLabels (τ i) (labels i.succ)
    let slot := giantTwoSidedPatternFreeSlot (C i j) ell l
    let D := giantTwoSidedPatternDilation (C i) s (aux i)
    (¬(s j slot).val ∣ D) ∧ (¬(t j slot).val ∣ D) := by
  have hs : MarkedPhysicalMarkingDistinct (giantTwoSidedPermuteLabels (π i) (labels i.castSucc)) :=
    fun g => (hguard.1 i.castSucc g).comp (π i g).injective
  have ht : MarkedPhysicalMarkingDistinct (giantTwoSidedPermuteLabels (τ i) (labels i.succ)) :=
    fun g => (hguard.1 i.succ g).comp (τ i g).injective
  exact ⟨giantTwoSidedLabelSourceFree_not_dvd hP hdis (hguard.2 i) hs j l,
    giantTwoSidedLabelTargetFree_not_dvd hP hdis (hguard.2 i) ht j l⟩

end
end ArtinMatthews
