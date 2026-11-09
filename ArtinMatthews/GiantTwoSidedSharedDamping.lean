module

public import ArtinMatthews.GiantTwoSidedRawEdgeCoordinates
public import ArtinMatthews.GiantTwoSidedSharedHits
public import ArtinMatthews.GiantTwoSidedSharedCollision


set_option backward.privateInPublic true
@[expose] public section

/-! The actual shared-list guard and both full damping factors remain
in the quotient. Off the literal collision event, they give the two
one-mark dampings exactly. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def GiantTwoSidedSharedAdmissible {J : Type*} {P : J → Finset ℕ} {k : ℕ}
    (c : MarkedPhysicalMarking P k) (b b' : (j : J) → ↥(P j)) : Prop :=
  MarkedPhysicalMarkingDistinct c ∧
    (∀ j,b j ∉ Set.range (c j)) ∧ ∀ j,b' j ∉ Set.range (c j)

def giantTwoSidedSharedGuardedDamping {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
    (q : ℝ) (w : ℕ) (b b' : (j : J) → ↥(P j)) (c : MarkedPhysicalMarking P k) : ℝ :=
  if GiantTwoSidedSharedAdmissible c b b' then
    (giantTwoSidedEndpointDamping P (k+1) q (markedPhysicalMarkingProduct c*w))^2 *
      (giantTwoSidedEndpointDamping P (k+1) q (markedPhysicalMarkingProduct c*(w+1)))^2
  else 0

def giantTwoSidedOneMarkDampingProduct {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (q : ℝ) (w : ℕ) : ℝ :=
  (giantTwoSidedEndpointDamping P 1 q w)^2 *
    (giantTwoSidedEndpointDamping P 1 q (w+1))^2

theorem giantTwoSidedShared_count_full {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) {k w : ℕ}
    (c : MarkedPhysicalMarking P k) (hc : MarkedPhysicalMarkingDistinct c)
    (b : (j : J) → ↥(P j)) (hb : ∀ j,b j ∉ Set.range (c j))
    (hw : ∀ j,(b j:ℕ) ∣ w) :
    (k+1)*Fintype.card J ≤ bandCount (univ.biUnion P) (markedPhysicalMarkingProduct c*w) := by
  apply giantTwoSidedEndpoint_count_le hdis ((markedPhysicalMarkingSplit k).symm (c,b))
    ((giantTwoSidedSplit_distinct_iff c b).mpr ⟨hc,hb⟩)
  exact (giantTwoSidedSplit_divisibility_iff c b).mpr
    ⟨fun j l => dvd_mul_of_dvd_left (giantTwoSidedSharedLabel_dvd_product c j l) w,
      fun j => dvd_mul_of_dvd_right (hw j) (markedPhysicalMarkingProduct c)⟩

theorem giantTwoSidedSharedAdmissible_of_good {J : Type*}
    {P : J → Finset ℕ} {k w : ℕ} (c : MarkedPhysicalMarking P k)
    (b b' : (j : J) → ↥(P j)) (hb : ∀ j,(b j:ℕ) ∣ w)
    (hb' : ∀ j,(b' j:ℕ) ∣ w+1) (hg : GiantTwoSidedSharedGood c w) :
    GiantTwoSidedSharedAdmissible c b b' := by
  refine ⟨hg.1,?_,?_⟩
  · rintro j ⟨l,he⟩
    apply hg.2 j l
    rw [he]
    exact dvd_mul_of_dvd_left (hb j) (w+1)
  · rintro j ⟨l,he⟩
    apply hg.2 j l
    rw [he]
    exact dvd_mul_of_dvd_right (hb' j) w

theorem giantTwoSidedSharedGuardedDamping_eq_of_good {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) {k w : ℕ}
    (c : MarkedPhysicalMarking P k) (b b' : (j : J) → ↥(P j))
    (hb : ∀ j,(b j:ℕ) ∣ w) (hb' : ∀ j,(b' j:ℕ) ∣ w+1)
    {q : ℝ} (hq : 0 ≤ q) (hg : GiantTwoSidedSharedGood c w) :
    giantTwoSidedSharedGuardedDamping q w b b' c = giantTwoSidedOneMarkDampingProduct P q w := by
  have ha := giantTwoSidedSharedAdmissible_of_good c b b' hb hb' hg
  have h1 := giantTwoSidedShared_damping_relation hP hdis c ha.1 w hq
    (giantTwoSidedShared_count_full hdis c ha.1 b ha.2.1 hb)
  have h2 := giantTwoSidedShared_damping_relation hP hdis c ha.1 (w+1) hq
    (giantTwoSidedShared_count_full hdis c ha.1 b' ha.2.2 hb')
  rw [giantTwoSidedSharedHits_eq_zero_of_avoids c w
      (fun j l h => hg.2 j l (dvd_mul_of_dvd_left h (w+1))),pow_zero,mul_one] at h1
  rw [giantTwoSidedSharedHits_eq_zero_of_avoids c (w+1)
      (fun j l h => hg.2 j l (dvd_mul_of_dvd_right h w)),pow_zero,mul_one] at h2
  rw [giantTwoSidedSharedGuardedDamping,ite_eq_left ha,giantTwoSidedOneMarkDampingProduct,h1,h2]

theorem giantTwoSidedSharedGuardedDamping_nonneg {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k w : ℕ} (q : ℝ)
    (b b' : (j : J) → ↥(P j)) (c : MarkedPhysicalMarking P k) :
    0 ≤ giantTwoSidedSharedGuardedDamping q w b b' c := by
  unfold giantTwoSidedSharedGuardedDamping
  split_ifs
  · positivity
  · exact le_rfl

theorem giantTwoSidedSharedGuardedDamping_le {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) {k w : ℕ}
    (c : MarkedPhysicalMarking P k) (b b' : (j : J) → ↥(P j))
    (hb : ∀ j,(b j:ℕ) ∣ w) (hb' : ∀ j,(b' j:ℕ) ∣ w+1)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    giantTwoSidedSharedGuardedDamping q w b b' c ≤
      (q⁻¹)^(2*(k*Fintype.card J))*giantTwoSidedOneMarkDampingProduct P q w := by
  unfold giantTwoSidedSharedGuardedDamping giantTwoSidedOneMarkDampingProduct
  split_ifs with ha
  · have h1 := giantTwoSidedShared_damping_le hP hdis c ha.1 w hq hq1
      (giantTwoSidedShared_count_full hdis c ha.1 b ha.2.1 hb)
    have h2 := giantTwoSidedShared_damping_le hP hdis c ha.1 (w+1) hq hq1
      (giantTwoSidedShared_count_full hdis c ha.1 b' ha.2.2 hb')
    calc
      _ ≤ _ := mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = _ := by rw [two_mul,pow_add]; ring
  · positivity

end
end ArtinMatthews
