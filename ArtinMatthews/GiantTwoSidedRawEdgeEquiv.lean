module

public import ArtinMatthews.GiantTwoSidedRawEdgeCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The original raw edges and their shared-list quotient coordinates
are in a literal finite equivalence. No label-order factor appears. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedRawSharedEquiv {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {k N : ℕ} {Z Z' : Finset ℕ} (hZ : Z ⊆ Ioc 0 N) :
    GiantTwoSidedRawPhysicalEdge P k Z Z' ≃ GiantTwoSidedRawSharedEdge P k N Z Z' where
  toFun := giantTwoSidedRawPhysical_to_shared hP hdis hZ
  invFun := giantTwoSidedRawShared_to_physical
  left_inv e := by
    let s := e.1.1
    let t := e.1.2
    let a := markedPhysicalMarkingSplit k s.1.2
    let a' := markedPhysicalMarkingSplit k t.1.2
    let D := markedPhysicalMarkingProduct a.1
    have hs : (markedPhysicalMarkingSplit k).symm (a.1,a.2) = s.1.2 :=
      (markedPhysicalMarkingSplit k).symm_apply_apply _
    have he : a.1=a'.1 ∧ t.1.1.val=s.1.1.val+D := e.2
    have ht : (markedPhysicalMarkingSplit k).symm (a.1,a'.2) = t.1.2 := by
      rw [he.1]
      exact (markedPhysicalMarkingSplit k).symm_apply_apply _
    have hc := (giantTwoSidedSplit_distinct_iff a.1 a.2).mp (by simpa only [hs] using s.2.1)
    have hd := (giantTwoSidedSplit_divisibility_iff a.1 a.2).mp (by simpa only [hs] using s.2.2)
    have hdiv : D ∣ s.1.1.val := markedPhysicalMarkingProduct_dvd hP hdis a.1 hc.1 hd.1
    have hn : D*(s.1.1.val/D)=s.1.1.val := Nat.mul_div_cancel' hdiv
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact hn
      · exact hs
    · apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        change D*(s.1.1.val/D+1)=t.1.1.val
        rw [Nat.mul_add,Nat.mul_one,hn,he.2]
      · exact ht
  right_inv a := by
    let c := a.1.1
    let w := a.1.2.1.val
    let b := a.1.2.2.1
    let b' := a.1.2.2.2
    let D := markedPhysicalMarkingProduct c
    have hD : 0 < D := markedPhysicalMarkingProduct_pos hP c
    have hb := (markedPhysicalMarkingSplit k).apply_symm_apply (c,b)
    have hb' := (markedPhysicalMarkingSplit k).apply_symm_apply (c,b')
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun a : MarkedPhysicalMarking P k × ((j : J) → ↥(P j)) => a.1) hb
    · apply Prod.ext
      · apply Subtype.ext
        change D*w / markedPhysicalMarkingProduct
          (markedPhysicalMarkingSplit k ((markedPhysicalMarkingSplit k).symm (c,b))).1 = w
        rw [hb]
        exact Nat.mul_div_cancel_left w hD
      · apply Prod.ext
        · exact congrArg (fun a : MarkedPhysicalMarking P k × ((j : J) → ↥(P j)) => a.2) hb
        · exact congrArg (fun a : MarkedPhysicalMarking P k × ((j : J) → ↥(P j)) => a.2) hb' 

theorem giantTwoSidedRawShared_sum {J A : Type*} [Fintype J] [DecidableEq J] [AddCommMonoid A]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {k N : ℕ} {Z Z' : Finset ℕ} (hZ : Z ⊆ Ioc 0 N)
    (F : GiantTwoSidedRawSharedEdge P k N Z Z' → A) :
    (∑ e : GiantTwoSidedRawPhysicalEdge P k Z Z',F (giantTwoSidedRawPhysical_to_shared hP hdis hZ e)) =
      ∑ a : GiantTwoSidedRawSharedEdge P k N Z Z',F a :=
  (giantTwoSidedRawSharedEquiv hP hdis hZ).sum_comp F

theorem giantTwoSidedRawShared_free_distinct {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) {k N : ℕ} {Z Z' : Finset ℕ}
    (a : GiantTwoSidedRawSharedEdge P k N Z Z') (j : J) :
    a.1.2.2.1 j ≠ a.1.2.2.2 j := by
  intro he
  have h : (a.1.2.2.1 j:ℕ) ∣ a.1.2.1.val := a.2.2.2.2.1 j
  have h' : (a.1.2.2.1 j:ℕ) ∣ a.1.2.1.val+1 := he ▸ a.2.2.2.2.2.1 j
  have hd := Nat.dvd_sub h' h
  rw [Nat.add_sub_cancel_left] at hd
  exact (hP j _ (a.1.2.2.1 j).property).not_dvd_one hd

end
end ArtinMatthews
