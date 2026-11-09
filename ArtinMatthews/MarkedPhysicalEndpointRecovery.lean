module

public import ArtinMatthews.MarkedPhysicalEndpointState


set_option backward.privateInPublic true
@[expose] public section

/-! Recovery of the original rough cofactor from a literal physical state.
The endpoint-support condition is equivalent to roughness of this quotient,
so both directions of the arithmetic lift are retained. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem markedPhysicalMarkingProduct_dvd {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    {u : ℕ} (hd : ∀ j k, (a j k : ℕ) ∣ u) : markedPhysicalMarkingProduct a ∣ u := by
  classical
  have hi := markedPhysicalMarking_global_injective hdis a ha
  rw [markedPhysicalMarkingProduct,
    ← Fintype.prod_prod_type (fun t : J × Fin M => (a t.1 t.2 : ℕ))]
  apply Fintype.prod_dvd_of_isRelPrime
  · intro i j hij
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes (hP _ _ (a i.1 i.2).2) (hP _ _ (a j.1 j.2).2)).mpr
      (fun h => hij (hi h))
  · intro i
    exact hd i.1 i.2

theorem markedPhysical_activeDivisors_of_support {J : Type*}
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M)
    (ha : MarkedPhysicalMarkingDistinct a) {u : ℕ}
    (hd : ∀ j k, (a j k : ℕ) ∣ u) (hu : MarkedPhysicalEndpointSupport P M u) (j : J) :
    activeDivisors (P j) u = markedPhysicalLabelSet a j := by
  have hs : markedPhysicalLabelSet a j ⊆ activeDivisors (P j) u := by
    intro p hp
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨(a j k).2, hd j k⟩
  apply (Finset.eq_of_subset_of_card_le hs ?_).symm
  rw [markedPhysicalLabelSet_card a ha j]
  exact (hu.1 j).le

theorem markedPhysicalSupportedProduct_of_support {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M)
    (ha : MarkedPhysicalMarkingDistinct a) {u : ℕ}
    (hd : ∀ j k, (a j k : ℕ) ∣ u) (hu : MarkedPhysicalEndpointSupport P M u) :
    markedPhysicalSupportedProduct P u = markedPhysicalMarkingProduct a := by
  unfold markedPhysicalSupportedProduct markedPhysicalMarkingProduct
  apply Finset.prod_congr rfl
  intro j _
  rw [markedPhysical_activeDivisors_of_support a ha hd hu j]
  exact Finset.prod_image (fun k _ l _ hkl => ha j (Subtype.ext hkl))

/-- Exact converse to the rough-cofactor construction, on the actual full
physical list. No independent source-identity premise remains. -/
theorem markedPhysicalEndpointSupport_iff_rough_quotient {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {M : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    {u : ℕ} (hd : ∀ j k, (a j k : ℕ) ∣ u) :
    MarkedPhysicalEndpointSupport P M u ↔
      MarkedPhysicalBandRough P (u / markedPhysicalMarkingProduct a) := by
  have hG := markedPhysicalMarkingProduct_dvd hP hdis a ha hd
  have heq : markedPhysicalMarkingProduct a * (u / markedPhysicalMarkingProduct a) = u :=
    Nat.mul_div_cancel' hG
  constructor
  · intro hu j p hp hpm
    have hpu : p ∣ u := hpm.trans (Nat.div_dvd_of_dvd hG)
    have hmem : p ∈ markedPhysicalLabelSet a j := by
      rw [← markedPhysical_activeDivisors_of_support a ha hd hu j]
      exact Finset.mem_filter.mpr ⟨hp, hpu⟩
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hmem
    have hpG : p ∣ markedPhysicalMarkingProduct a :=
      (markedPhysicalMarkingProduct_prime_dvd_iff hP a (hP j p hp)).mpr ⟨j, k, hk.symm⟩
    apply hu.2 j p hp
    simpa only [pow_two, heq] using mul_dvd_mul hpG hpm
  · intro hm
    simpa only [heq] using markedPhysicalEndpointSupport_mul hP hdis a ha hm

theorem markedPhysicalState_product_dvd {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (s : MarkedPhysicalState P M Z) :
    markedPhysicalMarkingProduct s.1.2 ∣ s.1.1.1.1.natAbs := by
  apply markedPhysicalMarkingProduct_dvd hP hdis s.1.2 s.2.2.1
  intro j k
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (s.2.2.2 j k)

theorem markedPhysicalState_support_iff {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (M : ℕ) (Z : Finset (ℤ × ℤ)) (s : MarkedPhysicalState P M Z) :
    MarkedPhysicalEndpointSupport P M s.1.1.1.1.natAbs ↔
      MarkedPhysicalBandRough P (s.1.1.1.1.natAbs / markedPhysicalMarkingProduct s.1.2) := by
  apply markedPhysicalEndpointSupport_iff_rough_quotient hP hdis s.1.2 s.2.2.1
  intro j k
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (s.2.2.2 j k)

end ArtinMatthews
