module

public import ArtinMatthews.GiantComparisonMarkingGuards


set_option backward.privateInPublic true
@[expose] public section

/-! Each copied hit costs at most one inverse damping factor per endpoint. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell : ℕ}
  {C : J → Finset (Fin k)}

private theorem join_damping_relation
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (c : GiantComparisonSharedLabels P C) {w : ℕ} (b : GiantComparisonFreeMarking P C ell w)
    (ha : MarkedPhysicalMarkingDistinct (giantComparisonJoinLabels c b.val))
    {q : ℝ} (hq : 0 ≤ q) :
    (giantTwoSidedEndpointDamping P (k+ell) q (giantComparisonSharedProduct c*w))^2 *
        q^(giantComparisonCopiedHits C (giantComparisonJoinLabels c b.val) w) =
      giantComparisonQuotientDamping P C ell q w := by
  rw [← giantComparisonSharedProduct_join c b.val]
  apply giantComparisonDamping_relation hP hdis C _ ha w _ hq
  intro j l
  rw [giantComparisonSharedProduct_join]
  exact giantComparisonJoinLabels_dvd c b.val w b.property.2 j l

theorem giantComparisonJoinDamping_le
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (c : GiantComparisonSharedLabels P C) {w : ℕ} (b : GiantComparisonFreeMarking P C ell w)
    (ha : MarkedPhysicalMarkingDistinct (giantComparisonJoinLabels c b.val))
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (giantTwoSidedEndpointDamping P (k+ell) q (giantComparisonSharedProduct c*w))^2 ≤
      giantComparisonQuotientDamping P C ell q w * (q⁻¹)^(k*Fintype.card J) := by
  let a := giantComparisonJoinLabels c b.val
  have he := join_damping_relation hP hdis c b ha hq.le
  have hsize : giantComparisonCopiedHits C a w ≤ k*Fintype.card J := by
    unfold giantComparisonCopiedHits
    rw [show k*Fintype.card J = ∑ _j : J,k by simp [Nat.mul_comm]]
    apply sum_le_sum
    intro j _
    exact (card_le_card inter_subset_left).trans
      ((giantTwoSidedPatternCopiedValues_card (P j) (C j) (a j) (ha j)).trans_le (Nat.sub_le _ _))
  calc
    _ = giantComparisonQuotientDamping P C ell q w / q^(giantComparisonCopiedHits C a w) :=
      (eq_div_iff (pow_ne_zero _ hq.ne')).mpr he
    _ = giantComparisonQuotientDamping P C ell q w * (q⁻¹)^(giantComparisonCopiedHits C a w) := by
      rw [div_eq_mul_inv, inv_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_inv₀ hq).mpr hq1) hsize)
      (pow_nonneg hq.le _)

private theorem join_damping_eq_of_avoids
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (c : GiantComparisonSharedLabels P C) {w : ℕ} (b : GiantComparisonFreeMarking P C ell w)
    (ha : MarkedPhysicalMarkingDistinct (giantComparisonJoinLabels c b.val))
    (havoid : ∀ j (i : ↥(univ \ C j)), ¬ (c j i:ℕ) ∣ w)
    {q : ℝ} (hq : 0 ≤ q) :
    (giantTwoSidedEndpointDamping P (k+ell) q (giantComparisonSharedProduct c*w))^2 =
      giantComparisonQuotientDamping P C ell q w := by
  have hh : giantComparisonCopiedHits C (giantComparisonJoinLabels c b.val) w = 0 := by
    apply giantComparisonCopiedHits_eq_zero
    intro j i hi
    let l : ↥(univ \ C j) := ⟨i,mem_sdiff.mpr ⟨mem_univ i,hi⟩⟩
    exact (giantComparisonJoinLabels_shared c b.val j l).symm ▸ havoid j l
  simpa only [hh, pow_zero, mul_one] using join_damping_relation hP hdis c b ha hq

def giantComparisonGuardedDamping (aux : GiantTwoSidedPatternAuxiliary P C)
    (q : ℝ) (w w' : ℕ) (b b' : GiantComparisonFreeLabels P C ell)
    (c : GiantComparisonSharedLabels P C) : ℝ :=
  if GiantComparisonSharedAdmissible aux c b b' then
    (giantTwoSidedEndpointDamping P (k+ell) q (giantComparisonSharedProduct c*w))^2 *
      (giantTwoSidedEndpointDamping P (k+ell) q (giantComparisonSharedProduct c*w'))^2
  else 0

def giantComparisonIndependentDamping (P : J → Finset ℕ) (C : J → Finset (Fin k))
    (ell : ℕ) (q : ℝ) (w w' : ℕ) : ℝ :=
  giantComparisonQuotientDamping P C ell q w * giantComparisonQuotientDamping P C ell q w'

theorem giantComparisonGuardedDamping_nonneg (aux : GiantTwoSidedPatternAuxiliary P C)
    (q : ℝ) (w w' : ℕ) (b b' : GiantComparisonFreeLabels P C ell)
    (c : GiantComparisonSharedLabels P C) : 0 ≤ giantComparisonGuardedDamping aux q w w' b b' c := by
  unfold giantComparisonGuardedDamping
  split_ifs <;> positivity

theorem giantComparisonGuardedDamping_eq_of_good
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (aux : GiantTwoSidedPatternAuxiliary P C) {w w' : ℕ}
    (b : GiantComparisonFreeMarking P C ell w) (b' : GiantComparisonFreeMarking P C ell w')
    (haux : GiantComparisonUnsharedAuxAvoids aux b.val b'.val)
    {c : GiantComparisonSharedLabels P C} (hg : GiantComparisonSharedGood aux w w' c)
    {q : ℝ} (hq : 0 ≤ q) :
    giantComparisonGuardedDamping aux q w w' b.val b'.val c =
      giantComparisonIndependentDamping P C ell q w w' := by
  have ha := giantComparisonSharedAdmissible_of_good aux b b' haux hg
  rw [giantComparisonGuardedDamping, ite_eq_left ha, giantComparisonIndependentDamping,
    join_damping_eq_of_avoids hP hdis c b ha.1 (fun j i => (hg.2.1 j i).1) hq,
    join_damping_eq_of_avoids hP hdis c b' ha.2.1 (fun j i => (hg.2.1 j i).2) hq]

theorem giantComparisonGuardedDamping_le
    (hP : ∀ j p, p ∈ P j → p.Prime) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (aux : GiantTwoSidedPatternAuxiliary P C) (c : GiantComparisonSharedLabels P C) {w w' : ℕ}
    (b : GiantComparisonFreeMarking P C ell w) (b' : GiantComparisonFreeMarking P C ell w')
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    giantComparisonGuardedDamping aux q w w' b.val b'.val c ≤
      (q⁻¹)^(2*(k*Fintype.card J))*giantComparisonIndependentDamping P C ell q w w' := by
  unfold giantComparisonGuardedDamping giantComparisonIndependentDamping
  split_ifs with ha
  · have h1 := giantComparisonJoinDamping_le hP hdis c b ha.1 hq hq1
    have h2 := giantComparisonJoinDamping_le hP hdis c b' ha.2.1 hq hq1
    calc
      _ ≤ _ := mul_le_mul h1 h2 (sq_nonneg _) (by unfold giantComparisonQuotientDamping; positivity)
      _ = _ := by rw [two_mul,pow_add]; ring
  · unfold giantComparisonQuotientDamping
    positivity

end
end ArtinMatthews
