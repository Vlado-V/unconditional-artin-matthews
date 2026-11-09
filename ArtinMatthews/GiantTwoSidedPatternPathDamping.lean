module

public import ArtinMatthews.GiantTwoSidedPatternPathOffsets
public import ArtinMatthews.MarkedPhysicalDampingSchedule


set_option backward.privateInPublic true
@[expose] public section

/-! The original half-dampings give the source visit schedule exactly.
Expressing the positive states through their actual signed offsets
retains each active congruence and every inactive-prime factor. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedEndpointDamping_eq_inactive {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M : ℕ} {q : ℝ} (hq : 0 ≤ q) {Z : Finset ℕ} (s : GiantTwoSidedEndpointState P M Z) :
    giantTwoSidedEndpointDamping P M q s.val.1.val =
      markedPhysicalInactivePrimeWeight P s.val.2 (Real.sqrt q) s.val.1.val := by
  have hsum : (∑ j,(markedPhysicalExtraPrimes s.val.2 j s.val.1.val).card)+M*Fintype.card J =
      ∑ j,bandCount (P j) s.val.1.val := by
    simp_rw [markedPhysical_extra_card s.val.2 s.property.1 s.property.2]
    simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm]
  unfold giantTwoSidedEndpointDamping
  rw [giantCandidateBandCount_union P hdis,← hsum,Nat.add_sub_cancel,
    Real.rpow_div_two_eq_sqrt _ hq,Real.rpow_natCast,markedPhysicalInactivePrimeWeight_pow]

theorem giantTwoSidedPatternPath_damping_schedule {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M n : ℕ} {q : ℝ} (hq : 0 ≤ q) {Z : Finset ℕ}
    (s : Fin (n+2) → GiantTwoSidedEndpointState P M Z) :
    (∏ i : Fin (n+1),giantTwoSidedEndpointDamping P M q (s i.castSucc).val.1.val*
      giantTwoSidedEndpointDamping P M q (s i.succ).val.1.val) =
      ∏ v : Fin (n+2),markedPhysicalInactivePrimeWeight P (s v).val.2
        (markedMemoryVisitQ q (n+1) v) (s v).val.1.val := by
  rw [marked_fin_edge_product n (fun v => giantTwoSidedEndpointDamping P M q (s v).val.1.val),
    ← marked_fin_visit_product n (fun v => giantTwoSidedEndpointDamping P M q (s v).val.1.val)]
  apply prod_congr rfl
  intro v _
  unfold markedMemoryVisitQ
  split_ifs
  · exact giantTwoSidedEndpointDamping_eq_inactive P hdis hq (s v)
  · rw [giantTwoSidedEndpointDamping_eq_inactive P hdis hq (s v),
      markedPhysicalInactivePrimeWeight_sqrt_sq P (s v).val.2 hq]

def giantTwoSidedPathResidueFactor {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {M n : ℕ} (labels : Fin (n+2) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+2) → ℤ) (root : ℤ) : ℝ :=
  ∏ v : Fin (n+2),
    (∏ j,∏ p∈markedPhysicalLabelSet (labels v) j,
      if (p:ℤ)∣root+offset v then (1:ℝ) else 0) *
    (∏ j,∏ p∈P j \ markedPhysicalLabelSet (labels v) j,
      if (p:ℤ)∣root+offset v then markedMemoryVisitQ q (n+1) v else 1)

theorem giantTwoSidedPatternPath_residue_factor {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {k ell n : ℕ} {C : Fin (n+1) → J → Finset (Fin k)} {Z : Finset ℕ}
    (s : Fin (n+2) → GiantTwoSidedEndpointState P (k+ell) Z)
    (π τ : Fin (n+1) → J → Equiv.Perm (Fin (k+ell)))
    (aux : ∀ i,GiantTwoSidedPatternAuxiliary P (C i)) (step : Fin (n+1) → ℤ)
    (h : ∀ i,GiantTwoSidedPatternCondition (C i) (step i)
      (giantTwoSidedEndpointPermute (π i) (s i.castSucc))
      (giantTwoSidedEndpointPermute (τ i) (s i.succ)) (aux i)) {q : ℝ} (hq : 0 ≤ q) :
    (∏ i : Fin (n+1),giantTwoSidedEndpointDamping P (k+ell) q (s i.castSucc).val.1.val*
      giantTwoSidedEndpointDamping P (k+ell) q (s i.succ).val.1.val) =
      giantTwoSidedPathResidueFactor P (fun v => (s v).val.2) q
        (giantTwoSidedPathOffset (giantTwoSidedPatternPathIncrement s π aux step)) ((s 0).val.1.val:ℤ) := by
  rw [giantTwoSidedPatternPath_damping_schedule P hdis hq]
  unfold giantTwoSidedPathResidueFactor
  apply prod_congr rfl
  intro v _
  have hpos := giantTwoSidedPatternPath_position s π τ aux step h v
  rw [← hpos]
  have hactive : (∏ j,∏ p∈markedPhysicalLabelSet (s v).val.2 j,
      if (p:ℤ)∣((s v).val.1.val:ℤ) then (1:ℝ) else 0)=1 := by
    apply prod_eq_one
    intro j _
    apply prod_eq_one
    intro p hp
    obtain ⟨l,_,rfl⟩ := mem_image.mp hp
    exact ite_eq_left (Int.natCast_dvd_natCast.mpr ((s v).property.2 j l))
  rw [hactive,one_mul]
  unfold markedPhysicalInactivePrimeWeight
  apply prod_congr rfl
  intro j _
  apply prod_congr rfl
  intro p _
  simp only [Int.natCast_dvd_natCast]

end
end ArtinMatthews
