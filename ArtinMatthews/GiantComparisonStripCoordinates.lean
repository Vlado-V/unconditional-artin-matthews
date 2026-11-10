module

public import ArtinMatthews.GiantComparisonStripLabels
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

/-! In quotient coordinates each endpoint keeps its original unshared
marking. Both physical position guards and the auxiliary exclusion survive. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} {P : J → Finset ℕ} {k ell N : ℕ}
  {C : J → Finset (Fin k)} {Z Z' : Finset ℕ}

abbrev GiantComparisonSharedData (P : J → Finset ℕ) (C : J → Finset (Fin k))
    (ell N : ℕ) :=
  GiantComparisonSharedLabels P C × ↥(Ioc 0 N) ×
    GiantComparisonFreeLabels P C ell × GiantComparisonFreeLabels P C ell

variable [Fintype J]

abbrev GiantComparisonPhysicalEdge (P : J → Finset ℕ) (C : J → Finset (Fin k))
    (ell : ℕ) (Z Z' : Finset ℕ) (aux : GiantTwoSidedPatternAuxiliary P C) :=
  {e : GiantTwoSidedEndpointState P (k+ell) Z × GiantTwoSidedEndpointState P (k+ell) Z' //
    GiantTwoSidedPatternCondition C 1 e.1 e.2 aux}

structure GiantComparisonSharedCondition (Z Z' : Finset ℕ)
    (aux : GiantTwoSidedPatternAuxiliary P C)
    (a : GiantComparisonSharedData P C ell N) : Prop where
  sourceDistinct : MarkedPhysicalMarkingDistinct (giantComparisonJoinLabels a.1 a.2.2.1)
  targetDistinct : MarkedPhysicalMarkingDistinct (giantComparisonJoinLabels a.1 a.2.2.2)
  sourceDivides : ∀ j i, (a.2.2.1 j i : ℕ) ∣ a.2.1.val
  targetDivides : ∀ j i, (a.2.2.2 j i : ℕ) ∣ a.2.1.val+giantTwoSidedPatternAuxiliaryProduct aux
  sourcePosition : giantComparisonSharedProduct a.1*a.2.1.val ∈ Z
  targetPosition : giantComparisonSharedProduct a.1*
    (a.2.1.val+giantTwoSidedPatternAuxiliaryProduct aux) ∈ Z'
  auxiliaryBan : ∀ g j (i : ↥(C g)) (l : Fin (k+ell)),
    (aux g i : ℕ) ≠ (giantComparisonJoinLabels a.1 a.2.2.1 j l : ℕ) ∧
      (aux g i : ℕ) ≠ (giantComparisonJoinLabels a.1 a.2.2.2 j l : ℕ)

abbrev GiantComparisonSharedEdge (P : J → Finset ℕ) (C : J → Finset (Fin k))
    (ell N : ℕ) (Z Z' : Finset ℕ) (aux : GiantTwoSidedPatternAuxiliary P C) :=
  {a : GiantComparisonSharedData P C ell N // GiantComparisonSharedCondition Z Z' aux a}

theorem giantComparisonJoinLabels_dvd (c : GiantComparisonSharedLabels P C)
    (b : GiantComparisonFreeLabels P C ell) (w : ℕ)
    (hb : ∀ j i, (b j i : ℕ) ∣ w) (j : J) (l : Fin (k+ell)) :
    (giantComparisonJoinLabels c b j l : ℕ) ∣ giantComparisonSharedProduct c*w := by
  refine Fin.addCases (m:=k) (n:=ell) ?_ ?_ l
  · intro i
    by_cases hi : i ∈ C j
    · let u : GiantTwoSidedPatternFreeSlots (C j) ell := Sum.inl ⟨i, hi⟩
      change (giantComparisonJoinLabels c b j (giantTwoSidedPatternFreeSlot (C j) ell u) : ℕ) ∣ _
      rw [giantComparisonJoinLabels_free]
      exact dvd_mul_of_dvd_right (hb j u) _
    · let u : ↥(univ \ C j) := ⟨i, mem_sdiff.mpr ⟨mem_univ i, hi⟩⟩
      change (giantComparisonJoinLabels c b j (Fin.castAdd ell u.val) : ℕ) ∣ _
      rw [giantComparisonJoinLabels_shared]
      exact dvd_mul_of_dvd_left (giantComparisonSharedLabel_dvd c j u) _
  · intro i
    let u : GiantTwoSidedPatternFreeSlots (C j) ell := Sum.inr i
    change (giantComparisonJoinLabels c b j (giantTwoSidedPatternFreeSlot (C j) ell u) : ℕ) ∣ _
    rw [giantComparisonJoinLabels_free]
    exact dvd_mul_of_dvd_right (hb j u) _

def giantComparisonShared_to_physical {aux : GiantTwoSidedPatternAuxiliary P C}
    (a : GiantComparisonSharedEdge P C ell N Z Z' aux) :
    GiantComparisonPhysicalEdge P C ell Z Z' aux := by
  let c := a.val.1
  let w := a.val.2.1.val
  let b := a.val.2.2.1
  let b' := a.val.2.2.2
  let D := giantComparisonSharedProduct c
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  let s : GiantTwoSidedEndpointState P (k+ell) Z :=
    ⟨(⟨D*w,a.property.sourcePosition⟩,giantComparisonJoinLabels c b),
      a.property.sourceDistinct,giantComparisonJoinLabels_dvd c b w a.property.sourceDivides⟩
  let t : GiantTwoSidedEndpointState P (k+ell) Z' :=
    ⟨(⟨D*(w+d),a.property.targetPosition⟩,giantComparisonJoinLabels c b'),
      a.property.targetDistinct,giantComparisonJoinLabels_dvd c b' (w+d) a.property.targetDivides⟩
  refine ⟨(s,t),?_,?_,a.property.auxiliaryBan⟩
  · intro j i hi
    let u : ↥(univ \ C j) := ⟨i,mem_sdiff.mpr ⟨mem_univ i,hi⟩⟩
    exact (giantComparisonJoinLabels_shared c b' j u).trans
      (giantComparisonJoinLabels_shared c b j u).symm
  · change ((D*(w+d):ℕ):ℤ) = ((D*w:ℕ):ℤ) + 1*
      ((giantTwoSidedPatternCopiedProduct C (giantComparisonJoinLabels c b)*d:ℕ):ℤ)
    rw [giantComparisonSharedProduct_join, Nat.mul_add, Nat.cast_add, one_mul]

theorem giantComparisonPhysical_step {aux : GiantTwoSidedPatternAuxiliary P C}
    (e : GiantComparisonPhysicalEdge P C ell Z Z' aux) :
    e.val.2.val.1.val = e.val.1.val.1.val +
      giantComparisonSharedProduct (giantComparisonSharedLabelsOf C e.val.1.val.2)*
        giantTwoSidedPatternAuxiliaryProduct aux := by
  rw [giantComparisonSharedProduct_eq_copied]
  have h := e.property.2.1
  rw [one_mul] at h
  exact_mod_cast h

def giantComparisonPhysical_to_shared (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (hZ : Z ⊆ Ioc 0 N)
    {aux : GiantTwoSidedPatternAuxiliary P C}
    (e : GiantComparisonPhysicalEdge P C ell Z Z' aux) :
    GiantComparisonSharedEdge P C ell N Z Z' aux := by
  let s := e.val.1
  let t := e.val.2
  let c := giantComparisonSharedLabelsOf C s.val.2
  let b := giantComparisonFreeLabelsOf C s.val.2
  let b' := giantComparisonFreeLabelsOf C t.val.2
  let D := giantComparisonSharedProduct c
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  let w := s.val.1.val/D
  have htc : giantComparisonSharedLabelsOf C t.val.2 = c := giantComparisonSharedLabelsOf_eq e.property.1
  have hs : giantComparisonJoinLabels c b = s.val.2 :=
    (giantComparisonLabelsEquiv (P:=P) C ell).symm_apply_apply s.val.2
  have ht : giantComparisonJoinLabels c b' = t.val.2 := by
    rw [← htc]
    exact (giantComparisonLabelsEquiv (P:=P) C ell).symm_apply_apply t.val.2
  have hd : D ∣ s.val.1.val := giantComparisonSharedProduct_dvd hP hdis C s.val.2 s.property.1 s.property.2
  have hDn : D*w = s.val.1.val := Nat.mul_div_cancel' hd
  have hDn' : D*(w+d) = t.val.1.val := by
    rw [Nat.mul_add,hDn]
    exact (giantComparisonPhysical_step e).symm
  have hn := mem_Ioc.mp (hZ s.val.1.property)
  have hw : w ∈ Ioc 0 N := mem_Ioc.mpr
    ⟨Nat.div_pos (Nat.le_of_dvd hn.1 hd) (giantComparisonSharedProduct_pos hP c),
      (Nat.div_le_self s.val.1.val D).trans hn.2⟩
  refine ⟨(c,⟨w,hw⟩,b,b'),?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hs] using s.property.1
  · simpa only [ht] using t.property.1
  · intro j i
    apply (giantComparisonFreeLabel_coprime hP hdis C s.val.2 s.property.1 j i).dvd_mul_left.mp
    change (b j i : ℕ) ∣ D*w
    rw [hDn]
    exact s.property.2 j _
  · intro j i
    have hco := giantComparisonFreeLabel_coprime hP hdis C t.val.2 t.property.1 j i
    rw [htc] at hco
    apply hco.dvd_mul_left.mp
    change (b' j i : ℕ) ∣ D*(w+d)
    rw [hDn']
    exact t.property.2 j _
  · change D*w ∈ Z
    rw [hDn]
    exact s.val.1.property
  · change D*(w+d) ∈ Z'
    rw [hDn']
    exact t.val.1.property
  · intro g j i l
    simpa only [hs,ht] using e.property.2.2 g j i l

end
end ArtinMatthews
