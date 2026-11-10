module

public import ArtinMatthews.GiantTwoSidedRootMoment
public import ArtinMatthews.GiantTwoSidedActiveResidueWeight
public import ArtinMatthews.GiantTwoSidedRootClass
public import ArtinMatthews.ScalarWeightedBonferroni
public import ArtinMatthews.GiantTwoSidedRootCRTCount
public import ArtinMatthews.GiantTwoSidedRootResidueSplit
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

/-! The exact fixed-label root count assembles into the original
weighted moment. Static label guards and the position-return test
remain outside the scalar CRT count. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def GiantTwoSidedStaticLabels {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i))
    (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell)) : Prop :=
  (∀ v,MarkedPhysicalMarkingDistinct (labels v)) ∧
    ∀ i,GiantTwoSidedLabelCompatible (C i)
      (giantTwoSidedPermuteLabels (π i) (labels i.castSucc))
      (giantTwoSidedPermuteLabels (τ i) (labels i.succ)) (aux i)

theorem giantTwoSidedRootAdmissible_iff_active {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    {I : Finset ℕ} (root : ↥I) (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell)) :
    GiantTwoSidedRootAdmissible C π τ aux step (root,labels) ↔
      GiantTwoSidedStaticLabels C π τ aux labels ∧
        GiantTwoSidedActiveRoot univ labels
          (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)) root.val := by
  constructor
  · intro h
    refine ⟨⟨h.distinct,h.compatible⟩,?_⟩
    intro v _ p hp
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hp
    obtain ⟨l,_,hl⟩ := mem_image.mp hj
    rw [← hl]
    exact h.divides v j l
  · rintro ⟨hs,ha⟩
    refine ⟨hs.1,hs.2,?_⟩
    intro v j l
    exact ha v (mem_univ v) (labels v j l).val
      (mem_biUnion.mpr ⟨j,mem_univ j,mem_image.mpr ⟨l,mem_univ l,rfl⟩⟩)

theorem giantTwoSidedRootWeight_zero_of_inactive {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell)
    {I : Finset ℕ} (root : ↥I) (labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell))
    (ha : ¬GiantTwoSidedActiveRoot univ labels
      (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)) root.val) :
    giantTwoSidedRootWeight C π τ aux step q ζ K (root,labels)=0 := by
  unfold giantTwoSidedRootWeight
  rw [giantTwoSidedRootResidueFactor_active hdis,ite_eq_right ha,Complex.ofReal_zero,mul_zero]

theorem giantTwoSidedRootMoment_static {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell)
    (I : Finset ℕ) :
    giantTwoSidedRootMoment C π τ aux step q ζ K I =
      ∑ labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell),
        if GiantTwoSidedStaticLabels C π τ aux labels ∧
            giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step) (Fin.last n)=0 then
          ∑ root : ↥I,giantTwoSidedRootWeight C π τ aux step q ζ K (root,labels) else 0 := by
  unfold giantTwoSidedRootMoment
  rw [sum_comm]
  apply sum_congr rfl
  intro labels _
  have hpoint (root : ↥I) :
      (if GiantTwoSidedRootAdmissible C π τ aux step (root,labels) ∧
          giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step) (Fin.last n)=0 then
        giantTwoSidedRootWeight C π τ aux step q ζ K (root,labels) else 0) =
      (if GiantTwoSidedStaticLabels C π τ aux labels ∧
          giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step) (Fin.last n)=0 then
        giantTwoSidedRootWeight C π τ aux step q ζ K (root,labels) else 0) := by
    rw [giantTwoSidedRootAdmissible_iff_active]
    by_cases ha : GiantTwoSidedActiveRoot univ labels
        (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)) root.val
    · simp only [ha,and_true]
    · rw [giantTwoSidedRootWeight_zero_of_inactive hdis C π τ aux step q ζ K root labels ha]
      simp only [ite_self]
  simp_rw [hpoint]
  by_cases hs : GiantTwoSidedStaticLabels C π τ aux labels ∧
      giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step) (Fin.last n)=0 <;>
    simp [hs]

theorem giantTwoSidedRootMoment_eq_scalar_counts {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell n : ℕ} (C : Fin n → J → Finset (Fin k))
    (π τ : Fin n → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin n → ℤ)
    (q : ℝ) (ζ : Fin n → ℝ) (K : ∀ i,GiantTwoSidedPatternCoefficient P (C i) ell)
    (lo hi : ℕ) :
    giantTwoSidedRootMoment C π τ aux step q ζ K (Ico lo hi) =
      ∑ labels : Fin (n+1) → MarkedPhysicalMarking P (k+ell),
        let offset := giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)
        if (GiantTwoSidedStaticLabels C π τ aux labels ∧ offset (Fin.last n)=0) ∧
            GiantTwoSidedActiveCompatible univ labels offset then
          giantTwoSidedRootScalar C labels π τ aux ζ K *
            (giantTwoSidedActiveResidueWeight univ labels (markedMemoryVisitQ q n) offset:ℂ) *
            (scalarWeightedResidueCountIco
              (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes univ labels)
              (giantTwoSidedResidueLossNat univ (markedMemoryVisitQ q n) offset)
              lo hi (giantTwoSidedActiveModulus labels) (giantTwoSidedRootClass hP labels offset):ℂ)
        else 0 := by
  rw [giantTwoSidedRootMoment_static hdis]
  apply sum_congr rfl
  intro labels _
  dsimp only
  let offset := giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C labels π aux step)
  have hsum : (∑ root : ↥(Ico lo hi),giantTwoSidedRootWeight C π τ aux step q ζ K (root,labels)) =
      giantTwoSidedRootScalar C labels π τ aux ζ K *
        (∑ root∈Ico lo hi,giantTwoSidedRootResidueFactor P labels q offset (root:ℤ):ℝ) := by
    simp only [giantTwoSidedRootWeight,← mul_sum,← Complex.ofReal_sum]
    exact congrArg (fun z : ℝ => giantTwoSidedRootScalar C labels π τ aux ζ K * (z:ℂ))
      (Finset.sum_coe_sort (Ico lo hi) (fun root : ℕ =>
        giantTwoSidedRootResidueFactor P labels q offset (root:ℤ)))
  by_cases hs : GiantTwoSidedStaticLabels C π τ aux labels ∧ offset (Fin.last n)=0
  · by_cases hc : GiantTwoSidedActiveCompatible univ labels offset
    · rw [ite_eq_left hs,ite_eq_left (And.intro hs hc),hsum,
        giantTwoSidedRootResidue_sum_eq_count hP hdis labels q offset hc lo hi,Complex.ofReal_mul,mul_assoc]
    · rw [ite_eq_left hs,ite_eq_right (fun h => hc h.2),hsum,
        giantTwoSidedRootResidue_sum_incompatible hdis labels q offset hc lo hi,Complex.ofReal_zero,mul_zero]
  · rw [ite_eq_right hs,ite_eq_right (fun h => hs h.1)]

end
end ArtinMatthews
