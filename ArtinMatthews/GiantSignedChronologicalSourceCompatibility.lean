module

public import ArtinMatthews.GiantSignedChronologicalStatic
public import ArtinMatthews.GiantSignedBirthDisplacement
public import ArtinMatthews.GiantSignedChronologicalAnchorHits
public import ArtinMatthews.GiantSignedChronologicalDistinctSupport
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

/-! A birth-distinct chronology yields the actual source offsets and
static label guard. -/
namespace ArtinMatthews
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell n : ℕ}
    {C : Fin n → B → Finset (Fin k)} {batch : Fin (n+1) → B → ℕ}
    (h : GiantSignedChronologicalChoices PS PB ell C batch) (κ : Fin n → ℤ)

theorem giantSignedChronologicalJoinedOffset_eq :
    giantSignedChronologicalJoinedOffset h κ = giantSignedChronologicalOffset κ h := by
  unfold giantSignedChronologicalJoinedOffset giantSignedChronologicalOffset
  exact congrArg giantTwoSidedPathOffset (funext (giantSignedChronologicalJoinedIncrement_eq h κ))

theorem giantSignedChronologicalJoinedStaticLabels_of_birthDistinct
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h)) :
    GiantTwoSidedStaticLabels (giantSignedChronologicalJoinedPattern C)
      (giantSignedChronologicalJoinedSourcePermutation h)
      (giantSignedChronologicalJoinedTargetPermutation h)
      (giantSignedChronologicalJoinedAuxiliary h) (giantSignedChronologicalJoinedLabels h) :=
  giantSignedChronologicalJoinedStaticLabels h κ ha.compatible
    (fun v => giantSignedChronologicalMarking_distinct h κ ha hd v)

theorem giantSignedChronologicalJoinedActiveCompatible
    (ha : GiantSignedChronologicalAdmissible κ h)
    (hd : GiantSignedBirthDistinct (giantSignedChronologicalBirthData h))
    (hSB : ∀ s b, Disjoint (PS s) (PB b)) :
    GiantTwoSidedActiveCompatible Finset.univ (giantSignedChronologicalJoinedLabels h)
      (giantSignedChronologicalJoinedOffset h κ) := by
  let labels := giantSignedChronologicalJoinedLabels h
  let o := giantSignedChronologicalJoinedOffset h κ
  intro p i _ hi
  let j := (giantTwoSidedActiveVisit Finset.univ labels p).val
  have hj : p.val ∈ markedPhysicalActivePrimes (labels j) :=
    giantTwoSidedActiveVisit_mem Finset.univ labels p
  change (o i : ZMod p.val) = (o j : ZMod p.val)
  obtain ⟨s,_,hs⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hs
  obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hb
  rcases s with s | s <;> rcases b with b | b
  · change ((h.state i).1.val.2 s u).val = p.val at hu
    change ((h.state j).1.val.2 b v).val = p.val at hv
    let pS : ↥(markedPhysicalBandPrimes PS) :=
      ⟨p.val, Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, hu ▸ ((h.state i).1.val.2 s u).property⟩⟩
    have hitI : pS.val ∈ markedPhysicalActivePrimes (h.state i).1.val.2 :=
      Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, Finset.mem_image.mpr ⟨u, Finset.mem_univ u, hu⟩⟩
    have hitJ : pS.val ∈ markedPhysicalActivePrimes (h.state j).1.val.2 :=
      Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hv⟩⟩
    exact add_left_cancel ((giantSignedChronologicalSmallActive_hit h κ ha.compatible i pS hitI).trans
      (giantSignedChronologicalSmallActive_hit h κ ha.compatible j pS hitJ).symm)
  · change ((h.state i).1.val.2 s u).val = p.val at hu
    change ((h.state j).2.1 b v).val = p.val at hv
    exact False.elim (Finset.disjoint_left.mp (hSB s b)
      (hu ▸ ((h.state i).1.val.2 s u).property) (hv ▸ ((h.state j).2.1 b v).property))
  · change ((h.state i).2.1 s u).val = p.val at hu
    change ((h.state j).1.val.2 b v).val = p.val at hv
    exact False.elim (Finset.disjoint_left.mp (hSB b s)
      (hv ▸ ((h.state j).1.val.2 b v).property) (hu ▸ ((h.state i).2.1 s u).property))
  · change ((h.state i).2.1 s u).val = p.val at hu
    change ((h.state j).2.1 b v).val = p.val at hv
    have he := giantSignedChronological_active_offsets κ h ha hd i j s b u v (hu.trans hv.symm)
    change (giantSignedChronologicalJoinedOffset h κ i : ZMod p.val) =
      (giantSignedChronologicalJoinedOffset h κ j : ZMod p.val)
    rw [giantSignedChronologicalJoinedOffset_eq h κ]
    exact hu ▸ he

end
end ArtinMatthews
