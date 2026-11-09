module

public import ArtinMatthews.GiantTwoSidedResiduePathLabels
public import ArtinMatthews.GiantTwoSidedPatternPathDamping


set_option backward.privateInPublic true
@[expose] public section

/-! The independent root-tuple factor retains every active-coordinate
indicator and the original endpoint/interior visit damping schedule. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedResidueActiveIndicator {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M)
    (r : GiantTwoSidedFullResidue P) : ℝ :=
  ∏ j,∏ p∈markedPhysicalLabelSet a j,if p∈giantTwoSidedResidueZeros r then 1 else 0

theorem giantTwoSidedResidueActiveIndicator_eq {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M)
    (r : GiantTwoSidedFullResidue P) :
    giantTwoSidedResidueActiveIndicator a r=
      if ∀ j l,r (giantTwoSidedResidueIndex j (a j l))=0 then 1 else 0 := by
  by_cases h : ∀ j l,r (giantTwoSidedResidueIndex j (a j l))=0
  · rw [ite_eq_left h]
    apply prod_eq_one
    intro j _
    apply prod_eq_one
    intro p hp
    obtain ⟨l,_,rfl⟩ := mem_image.mp hp
    exact ite_eq_left ((mem_giantTwoSidedResidueZeros r _).mpr (h j l))
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨j,l,hl⟩ := h
    apply prod_eq_zero (mem_univ j)
    apply prod_eq_zero (mem_image.mpr ⟨l,mem_univ l,rfl⟩)
    exact ite_eq_right (fun hz => hl ((mem_giantTwoSidedResidueZeros r _).mp hz))

def giantTwoSidedResidueInactiveWeight {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M : ℕ} (a : MarkedPhysicalMarking P M)
    (q : ℝ) (r : GiantTwoSidedFullResidue P) : ℝ :=
  ∏ j,∏ p∈P j \ markedPhysicalLabelSet a j,if p∈giantTwoSidedResidueZeros r then q else 1

theorem giantTwoSidedResidueInactiveWeight_eq_physical {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (a : MarkedPhysicalMarking P M) (q : ℝ) (r : GiantTwoSidedFullResidue P) :
    giantTwoSidedResidueInactiveWeight P a q r=
      markedPhysicalInactivePrimeWeight P a q (giantTwoSidedResidueZeroProduct r) := by
  apply prod_congr rfl
  intro j _
  apply prod_congr rfl
  intro p hp
  let p' := giantTwoSidedResidueIndex j ⟨p,(mem_sdiff.mp hp).1⟩
  have hz : p∈giantTwoSidedResidueZeros r ↔ p∣giantTwoSidedResidueZeroProduct r :=
    (mem_giantTwoSidedResidueZeros r p').trans (giantTwoSidedResidueZeroProduct_dvd_iff hP r p').symm
  simp only [hz]

theorem giantTwoSidedResidueDamping_eq_inactive {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (s : GiantTwoSidedResidueState P M) :
    giantTwoSidedResidueDamping P M q s.val.1=
      giantTwoSidedResidueInactiveWeight P s.val.2 (Real.sqrt q) s.val.1 := by
  let n := giantTwoSidedResidueZeroProduct s.val.1
  let t : GiantTwoSidedEndpointState P M {n} :=
    ⟨(⟨n,mem_singleton_self n⟩,s.val.2),s.property.1,
      fun j l => (giantTwoSidedResidueZeroProduct_dvd_iff hP s.val.1
        (giantTwoSidedResidueIndex j (s.val.2 j l))).mpr (s.property.2 j l)⟩
  rw [giantTwoSidedResidueDamping_eq_physical hP,
    giantTwoSidedResidueInactiveWeight_eq_physical hP]
  exact giantTwoSidedEndpointDamping_eq_inactive P hdis hq t

theorem giantTwoSidedResidueInactiveWeight_sqrt_sq {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) {M : ℕ}
    (a : MarkedPhysicalMarking P M) {q : ℝ} (hq : 0 ≤ q) (r : GiantTwoSidedFullResidue P) :
    (giantTwoSidedResidueInactiveWeight P a (Real.sqrt q) r)^2=
      giantTwoSidedResidueInactiveWeight P a q r := by
  simp only [giantTwoSidedResidueInactiveWeight_eq_physical hP]
  exact markedPhysicalInactivePrimeWeight_sqrt_sq P a hq _

theorem giantTwoSidedResiduePath_damping_schedule {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M n : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (s : Fin (n+2) → GiantTwoSidedResidueState P M) :
    (∏ i : Fin (n+1),giantTwoSidedResidueDamping P M q (s i.castSucc).val.1*
      giantTwoSidedResidueDamping P M q (s i.succ).val.1)=
      ∏ v : Fin (n+2),giantTwoSidedResidueInactiveWeight P (s v).val.2
        (markedMemoryVisitQ q (n+1) v) (s v).val.1 := by
  rw [marked_fin_edge_product n (fun v => giantTwoSidedResidueDamping P M q (s v).val.1),
    ← marked_fin_visit_product n (fun v => giantTwoSidedResidueDamping P M q (s v).val.1)]
  apply prod_congr rfl
  intro v _
  unfold markedMemoryVisitQ
  split_ifs
  · exact giantTwoSidedResidueDamping_eq_inactive hP hdis hq (s v)
  · rw [giantTwoSidedResidueDamping_eq_inactive hP hdis hq (s v),
      giantTwoSidedResidueInactiveWeight_sqrt_sq hP (s v).val.2 hq]

def giantTwoSidedIndependentResidueFactor {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ) (root : GiantTwoSidedFullResidue P) : ℝ :=
  ∏ v : Fin (n+1),
    giantTwoSidedResidueActiveIndicator (labels v) (giantTwoSidedResidueTranslate (offset v) root)*
      giantTwoSidedResidueInactiveWeight P (labels v) (markedMemoryVisitQ q n v)
        (giantTwoSidedResidueTranslate (offset v) root)

theorem giantTwoSidedIndependentResidueFactor_nonneg {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    {q : ℝ} (hq : 0 ≤ q) (offset : Fin (n+1) → ℤ) (root : GiantTwoSidedFullResidue P) :
    0 ≤ giantTwoSidedIndependentResidueFactor P labels q offset root := by
  apply prod_nonneg
  intro v _
  apply mul_nonneg
  · exact prod_nonneg fun _ _ => prod_nonneg fun _ _ => by split_ifs <;> norm_num
  · apply prod_nonneg
    intro j _
    apply prod_nonneg
    intro p _
    split_ifs
    · unfold markedMemoryVisitQ
      split_ifs
      · exact Real.sqrt_nonneg q
      · exact hq
    · norm_num

theorem giantTwoSidedIndependentResidueFactor_zero {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ) (root : GiantTwoSidedFullResidue P)
    (h : ¬∀ v j l,giantTwoSidedResidueTranslate (offset v) root
      (giantTwoSidedResidueIndex j (labels v j l))=0) :
    giantTwoSidedIndependentResidueFactor P labels q offset root=0 := by
  push Not at h
  obtain ⟨v,j,l,hl⟩ := h
  apply prod_eq_zero (mem_univ v)
  have hv : ¬∀ g a,giantTwoSidedResidueTranslate (offset v) root
      (giantTwoSidedResidueIndex g (labels v g a))=0 := fun hh => hl (hh j l)
  rw [giantTwoSidedResidueActiveIndicator_eq,ite_eq_right hv,zero_mul]

theorem giantTwoSidedResidueRoot_damping_factor {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {k ell n : ℕ}
    {C : Fin (n+1) → J → Finset (Fin k)}
    {π τ : Fin (n+1) → J → Equiv.Perm (Fin (k+ell))}
    {aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)} {step : Fin (n+1) → ℤ}
    (d : GiantTwoSidedResidueRootPath C π τ aux step) {q : ℝ} (hq : 0 ≤ q) :
    (∏ i : Fin (n+1),giantTwoSidedResidueDamping P (k+ell) q
        (giantTwoSidedResidueRoot_reconstruct d i.castSucc).val.1*
      giantTwoSidedResidueDamping P (k+ell) q (giantTwoSidedResidueRoot_reconstruct d i.succ).val.1)=
      giantTwoSidedIndependentResidueFactor P d.val.2 q
        (giantTwoSidedPathOffset (giantTwoSidedLabelIncrement C d.val.2 π aux step)) d.val.1 := by
  rw [giantTwoSidedResiduePath_damping_schedule hP hdis hq]
  apply prod_congr rfl
  intro v _
  have ha : giantTwoSidedResidueActiveIndicator (d.val.2 v)
      (giantTwoSidedResidueRootPosition C π aux step d.val v)=1 := by
    rw [giantTwoSidedResidueActiveIndicator_eq,ite_eq_left (d.property.active v)]
  change _=giantTwoSidedResidueActiveIndicator (d.val.2 v)
    (giantTwoSidedResidueRootPosition C π aux step d.val v)*_
  rw [ha,one_mul]
  rfl

end
end ArtinMatthews
