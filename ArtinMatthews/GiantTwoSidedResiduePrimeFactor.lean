module

public import ArtinMatthews.GiantTwoSidedResiduePathFactor
public import ArtinMatthews.GiantTwoSidedActiveResidueWeight
public import ArtinMatthews.ScalarWeightedResidueCRT


set_option backward.privateInPublic true
@[expose] public section

/-! Each Haar prime coordinate carries the literal active indicators and
inactive visit factors. Used coordinates have one forced residue. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedResidueVisitFactor {J : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) (q : ℝ) (r : GiantTwoSidedFullResidue P) (p : ℕ) : ℝ :=
  if p∈markedPhysicalActivePrimes a then
    if p∈giantTwoSidedResidueZeros r then 1 else 0
  else if p∈giantTwoSidedResidueZeros r then q else 1

theorem giantTwoSidedResidueVisitFactor_product {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M : ℕ}
    (a : MarkedPhysicalMarking P M) (q : ℝ) (r : GiantTwoSidedFullResidue P) :
    giantTwoSidedResidueActiveIndicator a r*giantTwoSidedResidueInactiveWeight P a q r=
      ∏ p∈markedPhysicalBandPrimes P,giantTwoSidedResidueVisitFactor a q r p := by
  unfold giantTwoSidedResidueActiveIndicator giantTwoSidedResidueInactiveWeight markedPhysicalBandPrimes
  rw [prod_biUnion (fun i _ j _ hij => hdis hij),← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  let f (p : ℕ) := giantTwoSidedResidueVisitFactor a q r p
  have hactive : (∏ p∈markedPhysicalLabelSet a j,if p∈giantTwoSidedResidueZeros r then (1:ℝ) else 0)=
      ∏ p∈markedPhysicalLabelSet a j,f p := by
    apply prod_congr rfl
    intro p hp
    have ha : p∈markedPhysicalActivePrimes a := mem_biUnion.mpr ⟨j,mem_univ j,hp⟩
    exact (ite_eq_left ha).symm
  have hinactive : (∏ p∈P j \ markedPhysicalLabelSet a j,if p∈giantTwoSidedResidueZeros r then q else 1)=
      ∏ p∈P j \ markedPhysicalLabelSet a j,f p := by
    apply prod_congr rfl
    intro p hp
    have ha : p∉markedPhysicalActivePrimes a := fun hh => (mem_sdiff.mp hp).2
      ((markedPhysicalActivePrimes_mem_group hdis a j (mem_sdiff.mp hp).1).mp hh)
    exact (ite_eq_right ha).symm
  rw [hactive,hinactive,mul_comm]
  exact prod_sdiff (markedPhysicalLabelSet_subset a j)

def giantTwoSidedIndependentPrimeFactor {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (r : Fin (n+1) → ℝ) (offset : Fin (n+1) → ℤ) (p : ℕ) (z : ZMod p) : ℝ :=
  ∏ v : Fin (n+1),if p∈markedPhysicalActivePrimes (labels v) then
    if z+(offset v:ZMod p)=0 then 1 else 0
  else if z+(offset v:ZMod p)=0 then r v else 1

theorem giantTwoSidedIndependentResidueFactor_product {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) (q : ℝ)
    (offset : Fin (n+1) → ℤ) (root : GiantTwoSidedFullResidue P) :
    giantTwoSidedIndependentResidueFactor P labels q offset root=
      ∏ p : ↥(markedPhysicalBandPrimes P),
        giantTwoSidedIndependentPrimeFactor labels (markedMemoryVisitQ q n) offset p.val (root p) := by
  unfold giantTwoSidedIndependentResidueFactor
  simp_rw [giantTwoSidedResidueVisitFactor_product hdis]
  rw [prod_comm]
  calc
    _ = ∏ p : ↥(markedPhysicalBandPrimes P),∏ v : Fin (n+1),
        giantTwoSidedResidueVisitFactor (labels v) (markedMemoryVisitQ q n v)
          (giantTwoSidedResidueTranslate (offset v) root) p.val :=
      (prod_coe_sort (markedPhysicalBandPrimes P) _).symm
    _ = _ := by
      apply prod_congr rfl
      intro p _
      apply prod_congr rfl
      intro v _
      have hz := mem_giantTwoSidedResidueZeros (giantTwoSidedResidueTranslate (offset v) root) p
      simp only [giantTwoSidedResidueVisitFactor,hz,giantTwoSidedResidueTranslate]

def giantTwoSidedIndependentPrimeMean {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (r : Fin (n+1) → ℝ) (offset : Fin (n+1) → ℤ) (p : ℕ) : ℝ :=
  if hp : p=0 then 0 else
    letI : NeZero p := ⟨hp⟩
    (∑ z : ZMod p,giantTwoSidedIndependentPrimeFactor labels r offset p z)/p

theorem giantTwoSidedIndependentPrimeMean_eq {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (r : Fin (n+1) → ℝ) (offset : Fin (n+1) → ℤ) (p : ℕ) [NeZero p] :
    giantTwoSidedIndependentPrimeMean labels r offset p=
      (∑ z : ZMod p,giantTwoSidedIndependentPrimeFactor labels r offset p z)/p := by
  simp [giantTwoSidedIndependentPrimeMean,NeZero.ne p]

theorem giantTwoSidedIndependentResidue_mean_product {J : Type*} [Fintype J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) (q : ℝ) (offset : Fin (n+1) → ℤ) :
    (∑ root : GiantTwoSidedFullResidue P,giantTwoSidedIndependentResidueFactor P labels q offset root)/
        Fintype.card (GiantTwoSidedFullResidue P)=
      ∏ p∈markedPhysicalBandPrimes P,
        giantTwoSidedIndependentPrimeMean labels (markedMemoryVisitQ q n) offset p := by
  simp_rw [giantTwoSidedIndependentResidueFactor_product hdis]
  rw [← Fintype.prod_sum (fun (p : ↥(markedPhysicalBandPrimes P)) (z : ZMod p.val) =>
    giantTwoSidedIndependentPrimeFactor labels (markedMemoryVisitQ q n) offset p.val z),Fintype.card_pi]
  simp only [ZMod.card,Nat.cast_prod,← prod_div_distrib]
  rw [← prod_coe_sort (markedPhysicalBandPrimes P)]
  apply prod_congr rfl
  intro p _
  exact (giantTwoSidedIndependentPrimeMean_eq labels _ offset p.val).symm

theorem giantTwoSidedIndependentPrimeFactor_unused {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (r : Fin (n+1) → ℝ) (offset : Fin (n+1) → ℤ) (p : ℕ)
    (hp : p∉markedPhysicalPathUsedPrimes univ labels) (z : ZMod p) :
    giantTwoSidedIndependentPrimeFactor labels r offset p z=
      1-giantTwoSidedResidueLoss univ r offset p z := by
  unfold giantTwoSidedIndependentPrimeFactor giantTwoSidedResidueLoss markedFiniteLineLoss
  rw [sub_sub_cancel]
  apply prod_congr rfl
  intro v _
  have ha : p∉markedPhysicalActivePrimes (labels v) :=
    fun hh => hp (mem_biUnion.mpr ⟨v,mem_univ v,hh⟩)
  have hz : z+(offset v:ZMod p)=0 ↔ -(offset v:ZMod p)=z := by
    constructor
    · intro h
      linear_combination -h
    · intro h
      rw [← h,neg_add_cancel]
  simp only [ha,ite_false,hz]

theorem giantTwoSidedIndependentPrimeMean_unused {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (r : Fin (n+1) → ℝ) (offset : Fin (n+1) → ℤ) (p : ℕ) [NeZero p]
    (hp : p∉markedPhysicalPathUsedPrimes univ labels) :
    giantTwoSidedIndependentPrimeMean labels r offset p=
      1-scalarWeightedResidueMean (giantTwoSidedResidueLossNat univ r offset) p := by
  have hs : (∑ z : ZMod p,giantTwoSidedResidueLoss univ r offset p z)=
      scalarWeightedResidueMass (giantTwoSidedResidueLossNat univ r offset) p := by
    symm
    unfold scalarWeightedResidueMass
    rw [← sum_coe_sort]
    exact (giantTwoSidedResidueRepresentative p).sum_comp (giantTwoSidedResidueLoss univ r offset p)
  rw [giantTwoSidedIndependentPrimeMean_eq]
  simp_rw [giantTwoSidedIndependentPrimeFactor_unused labels r offset p hp]
  rw [sum_sub_distrib,hs]
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_one]
  rw [sub_div,div_self (Nat.cast_ne_zero.mpr (NeZero.ne p))]
  rfl

theorem giantTwoSidedIndependentPrimeFactor_used {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (r : Fin (n+1) → ℝ) (offset : Fin (n+1) → ℤ)
    (hc : GiantTwoSidedActiveCompatible univ labels offset)
    (p : ↥(markedPhysicalPathUsedPrimes univ labels)) (z : ZMod p.val) :
    giantTwoSidedIndependentPrimeFactor labels r offset p.val z=
      if z=giantTwoSidedActiveResidue univ labels offset p then
        ∏ v : Fin (n+1),if p.val∈markedPhysicalActivePrimes (labels v) then 1 else
          if (offset v:ZMod p.val)=(offset (giantTwoSidedActiveVisit univ labels p).val:ZMod p.val) then r v else 1
      else 0 := by
  by_cases hz : z=giantTwoSidedActiveResidue univ labels offset p
  · rw [ite_eq_left hz]
    unfold giantTwoSidedIndependentPrimeFactor
    apply prod_congr rfl
    intro v _
    have hh : z+(offset v:ZMod p.val)=0 ↔
        (offset v:ZMod p.val)=(offset (giantTwoSidedActiveVisit univ labels p).val:ZMod p.val) := by
      rw [hz]
      unfold giantTwoSidedActiveResidue
      constructor
      · intro h
        linear_combination h
      · intro h
        rw [h,neg_add_cancel]
    by_cases ha : p.val∈markedPhysicalActivePrimes (labels v)
    · rw [ite_eq_left ha,ite_eq_left ha,ite_eq_left (hh.mpr (hc p v (mem_univ v) ha))]
    · rw [ite_eq_right ha,ite_eq_right ha]
      simp only [hh]
  · rw [ite_eq_right hz]
    unfold giantTwoSidedIndependentPrimeFactor
    apply prod_eq_zero (mem_univ (giantTwoSidedActiveVisit univ labels p).val)
    rw [ite_eq_left (giantTwoSidedActiveVisit_mem univ labels p)]
    apply ite_eq_right
    intro hh
    apply hz
    unfold giantTwoSidedActiveResidue
    linear_combination hh

theorem giantTwoSidedIndependentPrimeMean_used {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (r : Fin (n+1) → ℝ) (offset : Fin (n+1) → ℤ)
    (hc : GiantTwoSidedActiveCompatible univ labels offset)
    (p : ↥(markedPhysicalPathUsedPrimes univ labels)) [NeZero p.val] :
    giantTwoSidedIndependentPrimeMean labels r offset p.val=
      (∏ v : Fin (n+1),if p.val∈markedPhysicalActivePrimes (labels v) then 1 else
        if (offset v:ZMod p.val)=(offset (giantTwoSidedActiveVisit univ labels p).val:ZMod p.val) then r v else 1)/p.val := by
  rw [giantTwoSidedIndependentPrimeMean_eq]
  simp only [giantTwoSidedIndependentPrimeFactor_used labels r offset hc p,
    sum_ite_eq',mem_univ,ite_true]

end
end ArtinMatthews
