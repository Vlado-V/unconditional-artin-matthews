module

public import ArtinMatthews.GiantTwoSidedSharedLists


set_option backward.privateInPublic true
@[expose] public section

/-! Literal raw edges have a shared prefix and advance by its full
product. The quotient coordinates retain both actual position tests
and the two original unshared labels. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def GiantTwoSidedRawPhysicalCondition {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k : ℕ} {Z Z' : Finset ℕ} (s : GiantTwoSidedEndpointState P (k+1) Z)
    (t : GiantTwoSidedEndpointState P (k+1) Z') : Prop :=
  let c := (markedPhysicalMarkingSplit k s.1.2).1
  c = (markedPhysicalMarkingSplit k t.1.2).1 ∧
    t.1.1.val = s.1.1.val+markedPhysicalMarkingProduct c

abbrev GiantTwoSidedRawPhysicalEdge {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (k : ℕ) (Z Z' : Finset ℕ) :=
  {e : GiantTwoSidedEndpointState P (k+1) Z × GiantTwoSidedEndpointState P (k+1) Z' //
    GiantTwoSidedRawPhysicalCondition e.1 e.2}

abbrev GiantTwoSidedRawSharedData {J : Type*} (P : J → Finset ℕ) (k N : ℕ) :=
  MarkedPhysicalMarking P k × ↥(Ioc 0 N) × ((j : J) → ↥(P j)) × ((j : J) → ↥(P j))

def GiantTwoSidedRawSharedCondition {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k N : ℕ} (Z Z' : Finset ℕ) (a : GiantTwoSidedRawSharedData P k N) : Prop :=
  let c := a.1
  let w := a.2.1.val
  let b := a.2.2.1
  let b' := a.2.2.2
  let D := markedPhysicalMarkingProduct c
  MarkedPhysicalMarkingDistinct c ∧
    (∀ j,b j ∉ Set.range (c j)) ∧ (∀ j,b' j ∉ Set.range (c j)) ∧
    (∀ j,(b j:ℕ) ∣ w) ∧ (∀ j,(b' j:ℕ) ∣ w+1) ∧ D*w ∈ Z ∧ D*(w+1) ∈ Z'

abbrev GiantTwoSidedRawSharedEdge {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (k N : ℕ) (Z Z' : Finset ℕ) :=
  {a : GiantTwoSidedRawSharedData P k N // GiantTwoSidedRawSharedCondition Z Z' a}

theorem giantTwoSidedSharedLabel_dvd_product {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k : ℕ} (c : MarkedPhysicalMarking P k) (j : J) (l : Fin k) :
    (c j l:ℕ) ∣ markedPhysicalMarkingProduct c :=
  (dvd_prod_of_mem (fun i : Fin k => (c j i:ℕ)) (mem_univ l)).trans
    (dvd_prod_of_mem (fun i : J => ∏ l : Fin k,(c i l:ℕ)) (mem_univ j))

def giantTwoSidedRawShared_to_physical {J : Type*} [Fintype J] {P : J → Finset ℕ}
    {k N : ℕ} {Z Z' : Finset ℕ} (a : GiantTwoSidedRawSharedEdge P k N Z Z') :
    GiantTwoSidedRawPhysicalEdge P k Z Z' := by
  let c := a.1.1
  let w := a.1.2.1.val
  let b := a.1.2.2.1
  let b' := a.1.2.2.2
  let D := markedPhysicalMarkingProduct c
  have ha : MarkedPhysicalMarkingDistinct c ∧
      (∀ j,b j ∉ Set.range (c j)) ∧ (∀ j,b' j ∉ Set.range (c j)) ∧
      (∀ j,(b j:ℕ) ∣ w) ∧ (∀ j,(b' j:ℕ) ∣ w+1) ∧ D*w ∈ Z ∧ D*(w+1) ∈ Z' := a.2
  let s : GiantTwoSidedEndpointState P (k+1) Z :=
    ⟨(⟨D*w,ha.2.2.2.2.2.1⟩,(markedPhysicalMarkingSplit k).symm (c,b)),
      (giantTwoSidedSplit_distinct_iff c b).mpr ⟨ha.1,ha.2.1⟩,
      (giantTwoSidedSplit_divisibility_iff c b).mpr
        ⟨fun j l => dvd_mul_of_dvd_left (giantTwoSidedSharedLabel_dvd_product c j l) w,
          fun j => dvd_mul_of_dvd_right (ha.2.2.2.1 j) D⟩⟩
  let t : GiantTwoSidedEndpointState P (k+1) Z' :=
    ⟨(⟨D*(w+1),ha.2.2.2.2.2.2⟩,(markedPhysicalMarkingSplit k).symm (c,b')),
      (giantTwoSidedSplit_distinct_iff c b').mpr ⟨ha.1,ha.2.2.1⟩,
      (giantTwoSidedSplit_divisibility_iff c b').mpr
        ⟨fun j l => dvd_mul_of_dvd_left (giantTwoSidedSharedLabel_dvd_product c j l) (w+1),
          fun j => dvd_mul_of_dvd_right (ha.2.2.2.2.1 j) D⟩⟩
  refine ⟨(s,t),?_⟩
  unfold GiantTwoSidedRawPhysicalCondition
  simp [s,t,Nat.mul_add,D]

def giantTwoSidedRawPhysical_to_shared {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (hP : ∀ j p,p∈P j → p.Prime) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {k N : ℕ} {Z Z' : Finset ℕ} (hZ : Z ⊆ Ioc 0 N)
    (e : GiantTwoSidedRawPhysicalEdge P k Z Z') : GiantTwoSidedRawSharedEdge P k N Z Z' := by
  let s := e.1.1
  let t := e.1.2
  let a := markedPhysicalMarkingSplit k s.1.2
  let a' := markedPhysicalMarkingSplit k t.1.2
  let c := a.1
  let b := a.2
  let b' := a'.2
  let D := markedPhysicalMarkingProduct c
  let n := s.1.1.val
  let n' := t.1.1.val
  let w := n/D
  have he : c=a'.1 ∧ n'=n+D := e.2
  have hs : (markedPhysicalMarkingSplit k).symm (c,b) = s.1.2 :=
    (markedPhysicalMarkingSplit k).symm_apply_apply _
  have ht : (markedPhysicalMarkingSplit k).symm (c,b') = t.1.2 := by
    rw [he.1]
    exact (markedPhysicalMarkingSplit k).symm_apply_apply _
  have hsd := (giantTwoSidedSplit_distinct_iff c b).mp (by simpa only [hs] using s.2.1)
  have htd := (giantTwoSidedSplit_distinct_iff c b').mp (by simpa only [ht] using t.2.1)
  have hsD := (giantTwoSidedSplit_divisibility_iff (n := n) c b).mp (by simpa only [hs] using s.2.2)
  have htD := (giantTwoSidedSplit_divisibility_iff (n := n') c b').mp (by simpa only [ht] using t.2.2)
  have hd : D ∣ n := markedPhysicalMarkingProduct_dvd hP hdis c hsd.1 hsD.1
  have hDn : D*w=n := Nat.mul_div_cancel' hd
  have hDn' : D*(w+1)=n' := by rw [Nat.mul_add,Nat.mul_one,hDn,he.2]
  have hn := mem_Ioc.mp (hZ s.1.1.property)
  have hw : w ∈ Ioc 0 N := mem_Ioc.mpr
    ⟨Nat.div_pos (Nat.le_of_dvd hn.1 hd) (markedPhysicalMarkingProduct_pos hP c),
      (Nat.div_le_self n D).trans hn.2⟩
  refine ⟨(c,⟨w,hw⟩,b,b'),hsd.1,hsd.2,htd.2,?_,?_,?_,?_⟩
  · intro j
    apply (giantTwoSidedShared_free_dvd_iff hP hdis c j (b j) (hsd.2 j) w).mp
    change (b j:ℕ) ∣ D*w
    rw [hDn]
    exact hsD.2 j
  · intro j
    apply (giantTwoSidedShared_free_dvd_iff hP hdis c j (b' j) (htd.2 j) (w+1)).mp
    change (b' j:ℕ) ∣ D*(w+1)
    rw [hDn']
    exact htD.2 j
  · change D*w ∈ Z
    rw [hDn]
    exact s.1.1.property
  · change D*(w+1) ∈ Z'
    rw [hDn']
    exact t.1.1.property

end
end ArtinMatthews
