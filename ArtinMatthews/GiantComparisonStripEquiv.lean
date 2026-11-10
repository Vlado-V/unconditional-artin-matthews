module

public import ArtinMatthews.GiantComparisonStripCoordinates
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

/-! The exact finite equivalence removes the shared product from both
positions and keeps every original ordering and auxiliary label. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell N : ℕ}
  {C : J → Finset (Fin k)} {Z Z' : Finset ℕ}
  {aux : GiantTwoSidedPatternAuxiliary P C}

def giantComparisonStripEquiv (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (hZ : Z ⊆ Ioc 0 N) :
    GiantComparisonPhysicalEdge P C ell Z Z' aux ≃ GiantComparisonSharedEdge P C ell N Z Z' aux where
  toFun := giantComparisonPhysical_to_shared hP hdis hZ
  invFun := giantComparisonShared_to_physical
  left_inv e := by
    let s := e.val.1
    let t := e.val.2
    let c := giantComparisonSharedLabelsOf C s.val.2
    let b := giantComparisonFreeLabelsOf C s.val.2
    let b' := giantComparisonFreeLabelsOf C t.val.2
    let D := giantComparisonSharedProduct c
    have htc : giantComparisonSharedLabelsOf C t.val.2 = c := giantComparisonSharedLabelsOf_eq e.property.1
    have hs : giantComparisonJoinLabels c b = s.val.2 :=
      (giantComparisonLabelsEquiv (P:=P) C ell).symm_apply_apply s.val.2
    have ht : giantComparisonJoinLabels c b' = t.val.2 := by
      rw [← htc]
      exact (giantComparisonLabelsEquiv (P:=P) C ell).symm_apply_apply t.val.2
    have hd : D ∣ s.val.1.val := giantComparisonSharedProduct_dvd hP hdis C s.val.2 s.property.1 s.property.2
    have hn : D*(s.val.1.val/D) = s.val.1.val := Nat.mul_div_cancel' hd
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (Subtype.ext hn) hs
    · apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        change D*(s.val.1.val/D+giantTwoSidedPatternAuxiliaryProduct aux) = t.val.1.val
        rw [Nat.mul_add,hn]
        exact (giantComparisonPhysical_step e).symm
      · exact ht
  right_inv a := by
    let c := a.val.1
    let w := a.val.2.1.val
    let b := a.val.2.2.1
    let b' := a.val.2.2.2
    let D := giantComparisonSharedProduct c
    have hD : 0 < D := giantComparisonSharedProduct_pos hP c
    have hs : giantComparisonSharedLabelsOf C (giantComparisonJoinLabels c b) = c := by
      funext j i
      exact giantComparisonJoinLabels_shared c b j i
    have hb (v : GiantComparisonFreeLabels P C ell) :
        giantComparisonFreeLabelsOf C (giantComparisonJoinLabels c v) = v := by
      funext j i
      exact giantComparisonJoinLabels_free c v j i
    apply Subtype.ext
    apply Prod.ext
    · exact hs
    · apply Prod.ext
      · apply Subtype.ext
        change D*w/giantComparisonSharedProduct (giantComparisonSharedLabelsOf C
          (giantComparisonJoinLabels c b)) = w
        rw [hs]
        exact Nat.mul_div_cancel_left w hD
      · exact Prod.ext (hb b) (hb b')

theorem giantComparisonStrip_sum {A : Type*} [DecidableEq J] [AddCommMonoid A]
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (hZ : Z ⊆ Ioc 0 N)
    (F : GiantComparisonSharedEdge P C ell N Z Z' aux → A) :
    (∑ e : GiantComparisonPhysicalEdge P C ell Z Z' aux,
        F (giantComparisonPhysical_to_shared hP hdis hZ e)) =
      ∑ a : GiantComparisonSharedEdge P C ell N Z Z' aux, F a :=
  (giantComparisonStripEquiv hP hdis hZ).sum_comp F

end
end ArtinMatthews
