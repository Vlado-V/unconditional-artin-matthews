module

public import ArtinMatthews.GiantComparisonStripKernel
public import ArtinMatthews.GiantTwoSidedSharedHits


set_option backward.privateInPublic true
@[expose] public section

/-! The exact discrepancy in the endpoint damping is the number of copied
primes already dividing the quotient. This keeps the overlap contribution
available while giving the literal variable-cardinality damping away from it. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell : ℕ}

def giantComparisonCopiedHits (C : J → Finset (Fin k))
    (a : MarkedPhysicalMarking P (k+ell)) (w : ℕ) : ℕ :=
  ∑ j, (giantTwoSidedPatternCopiedValues (P j) (C j) (a j) ∩ activeDivisors (P j) w).card

def giantComparisonQuotientDamping (P : J → Finset ℕ) (C : J → Finset (Fin k))
    (ell : ℕ) (q : ℝ) (w : ℕ) : ℝ :=
  q^(bandCount (univ.biUnion P) w-∑ j, (ell+(C j).card))

theorem giantComparisonCopied_activeDivisors_mul
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell)) (j : J) (w : ℕ) :
    activeDivisors (P j) (giantTwoSidedPatternCopiedProduct C a*w) =
      giantTwoSidedPatternCopiedValues (P j) (C j) (a j) ∪ activeDivisors (P j) w := by
  ext p
  simp only [activeDivisors, mem_filter, mem_union]
  constructor
  · rintro ⟨hp, h⟩
    rcases (hP j p hp).dvd_mul.mp h with hd | hw
    · exact Or.inl ((giantTwoSidedPatternCopiedProduct_dvd_iff hP hdis C a j hp).mp hd)
    · exact Or.inr ⟨hp, hw⟩
  · rintro (hc | ⟨hp, hw⟩)
    · obtain ⟨i, hi, he⟩ := mem_image.mp hc
      have hp : p ∈ P j := he ▸ (a j (Fin.castAdd ell i)).property
      exact ⟨hp, dvd_mul_of_dvd_left
        ((giantTwoSidedPatternCopiedProduct_dvd_iff hP hdis C a j hp).mpr (mem_image.mpr ⟨i,hi,he⟩)) w⟩
    · exact ⟨hp, dvd_mul_of_dvd_right hw _⟩

theorem giantComparisonCopied_count_add
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (ha : MarkedPhysicalMarkingDistinct a) (w : ℕ) :
    bandCount (univ.biUnion P) (giantTwoSidedPatternCopiedProduct C a*w) +
        giantComparisonCopiedHits C a w =
      (∑ j, (univ \ C j).card) + bandCount (univ.biUnion P) w := by
  rw [giantCandidateBandCount_union P hdis (giantTwoSidedPatternCopiedProduct C a*w),
    giantCandidateBandCount_union P hdis w, giantComparisonCopiedHits,
    ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  unfold bandCount
  rw [giantComparisonCopied_activeDivisors_mul hP hdis C a j w, card_union_add_card_inter,
    giantTwoSidedPatternCopiedValues_card (P j) (C j) (a j) (ha j),
    card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]

theorem giantComparisonCopiedHits_eq_zero
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell)) (w : ℕ)
    (hw : ∀ j (i : Fin k), i ∉ C j → ¬ (a j (Fin.castAdd ell i) : ℕ) ∣ w) :
    giantComparisonCopiedHits C a w = 0 := by
  unfold giantComparisonCopiedHits
  apply sum_eq_zero
  intro j _
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨i, hi, he⟩ := mem_image.mp (mem_inter.mp hp).1
  exact hw j i (mem_sdiff.mp hi).2 (he.symm ▸ (mem_filter.mp (mem_inter.mp hp).2).2)

theorem giantComparisonFree_count_le
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (ha : MarkedPhysicalMarkingDistinct a) (w : ℕ)
    (hd : ∀ j l, (a j l : ℕ) ∣ giantTwoSidedPatternCopiedProduct C a*w) (j : J) :
    ell+(C j).card ≤ bandCount (P j) w := by
  have hs : markedPhysicalLabelSet a j ⊆ activeDivisors (P j) (giantTwoSidedPatternCopiedProduct C a*w) := by
    intro p hp
    obtain ⟨l, _, rfl⟩ := mem_image.mp hp
    exact mem_filter.mpr ⟨(a j l).property, hd j l⟩
  have hfull := card_le_card hs
  rw [markedPhysicalLabelSet_card a ha j, giantComparisonCopied_activeDivisors_mul hP hdis C a j w] at hfull
  have hb := card_union_le (giantTwoSidedPatternCopiedValues (P j) (C j) (a j)) (activeDivisors (P j) w)
  rw [giantTwoSidedPatternCopiedValues_card (P j) (C j) (a j) (ha j)] at hb
  have hc := giantComparisonSlotCard (C j) ell
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin] at hc
  change _ ≤ (activeDivisors (P j) w).card
  omega

theorem giantComparisonQuotientDamping_eq_group_counts
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (ha : MarkedPhysicalMarkingDistinct a) (w : ℕ)
    (hd : ∀ j l, (a j l : ℕ) ∣ giantTwoSidedPatternCopiedProduct C a*w) (q : ℝ) :
    giantComparisonQuotientDamping P C ell q w =
      q^(∑ j, (bandCount (P j) w-(ell+(C j).card))) := by
  unfold giantComparisonQuotientDamping
  rw [giantCandidateBandCount_union P hdis w,
    sum_tsub_distrib univ (fun j _ => giantComparisonFree_count_le hP hdis C a ha w hd j)]

theorem giantComparisonDamping_relation
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (ha : MarkedPhysicalMarkingDistinct a) (w : ℕ)
    (hd : ∀ j l, (a j l : ℕ) ∣ giantTwoSidedPatternCopiedProduct C a*w)
    {q : ℝ} (hq : 0 ≤ q) :
    (giantTwoSidedEndpointDamping P (k+ell) q (giantTwoSidedPatternCopiedProduct C a*w))^2 *
        q^(giantComparisonCopiedHits C a w) =
      giantComparisonQuotientDamping P C ell q w := by
  have hfull := giantTwoSidedEndpoint_count_le hdis a ha hd
  have hcount := giantComparisonCopied_count_add hP hdis C a ha w
  have hslots : (∑ j, (univ \ C j).card)+(∑ j, (ell+(C j).card)) =
      (k+ell)*Fintype.card J := by
    rw [← sum_add_distrib]
    simp_rw [giantComparisonSlotCard]
    simp [Nat.mul_comm]
  have hexponent :
      (bandCount (univ.biUnion P) (giantTwoSidedPatternCopiedProduct C a*w) - (k+ell)*Fintype.card J) +
        giantComparisonCopiedHits C a w =
      bandCount (univ.biUnion P) w - ∑ j, (ell+(C j).card) := by omega
  rw [giantTwoSidedEndpointDamping_square P (k+ell) _ hq, ← pow_add, hexponent]
  rfl

theorem giantComparisonDamping_eq_no_copied_hit
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (C : J → Finset (Fin k)) (a : MarkedPhysicalMarking P (k+ell))
    (ha : MarkedPhysicalMarkingDistinct a) (w : ℕ)
    (hd : ∀ j l, (a j l : ℕ) ∣ giantTwoSidedPatternCopiedProduct C a*w)
    {q : ℝ} (hq : 0 ≤ q)
    (hw : ∀ j (i : Fin k), i ∉ C j → ¬ (a j (Fin.castAdd ell i) : ℕ) ∣ w) :
    (giantTwoSidedEndpointDamping P (k+ell) q (giantTwoSidedPatternCopiedProduct C a*w))^2 =
      giantComparisonQuotientDamping P C ell q w := by
  simpa only [giantComparisonCopiedHits_eq_zero C a w hw, pow_zero, mul_one] using
    giantComparisonDamping_relation hP hdis C a ha w hd hq

end
end ArtinMatthews
