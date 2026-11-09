module

public import ArtinMatthews.MarkedRepresentedDivisors
public import ArtinMatthews.MarkedProgressionWeighted


set_option backward.privateInPublic true
@[expose] public section

/-! Exact passage from disjoint represented marking bands to a single
prime-dependent residual. Repeated bands use exponent two, and their
selected prime sets retain collisions. -/

namespace ArtinMatthews

open scoped BigOperators

theorem selected_union_active_iff {ι : Type*} (I : Finset ι)
    (P S : ι → Finset ℕ) (hS : ∀ i ∈ I, S i ⊆ P i) (u : ℕ) :
    I.biUnion S ⊆ activeDivisors (I.biUnion P) u ↔
      ∀ i ∈ I, S i ⊆ activeDivisors (P i) u := by
  classical
  constructor
  · intro h i hi p hp
    have hpu := h (Finset.mem_biUnion.mpr ⟨i, hi, hp⟩)
    exact Finset.mem_filter.mpr ⟨hS i hi hp, (Finset.mem_filter.mp hpu).2⟩
  · intro h p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hpiP, hpu⟩ := Finset.mem_filter.mp (h i hi hpi)
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, hi, hpiP⟩, hpu⟩

theorem disjoint_bands_residual_union {ι : Type*} (I : Finset ι)
    (P S : ι → Finset ℕ) (hdis : Set.PairwiseDisjoint (↑I) P)
    (hS : ∀ i ∈ I, S i ⊆ P i) :
    (I.biUnion P) \ I.biUnion S = I.biUnion (fun i => P i \ S i) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hpS⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hpP
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_sdiff.mpr
      ⟨hpi, fun hs => hpS (Finset.mem_biUnion.mpr ⟨i, hi, hs⟩)⟩⟩
  · intro hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hpiP, hpiS⟩ := Finset.mem_sdiff.mp hpi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i, hi, hpiP⟩, ?_⟩
    intro hpS
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hpS
    by_cases hij : i = j
    · subst j
      exact hpiS hpj
    · exact Finset.disjoint_left.mp (hdis hi hj hij) hpiP (hS j hj hpj)

theorem representedBandTerm_eq_weightedResidual (P S : Finset ℕ)
    (u a : ℕ) (ρ : ℝ) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, θ p = 1 - ρ ^ a) :
    representedBandTerm P S u a ρ =
      ρ ^ (a * (S.card - 1)) * markedWeightedResidual P S θ u := by
  classical
  unfold representedBandTerm markedWeightedResidual
  split_ifs with hs
  · congr 1
    unfold representedBandResidual
    apply Finset.prod_congr rfl
    intro p hp
    rw [markedWeightedInput, hθ p (Finset.mem_sdiff.mp hp).1]
  · simp

/-- The exact multi-band identity used before one Bonferroni expansion.
The exponent can vary between one and two (or be any natural number), so
cross moments and repeated-array moments are covered by the same theorem. -/
theorem represented_bands_eq_single_residual {ι : Type*} (I : Finset ι)
    (P S : ι → Finset ℕ) (a : ι → ℕ) (ρ : ℝ) (θ : ℕ → ℝ)
    (hdis : Set.PairwiseDisjoint (↑I) P) (hS : ∀ i ∈ I, S i ⊆ P i)
    (hθ : ∀ i ∈ I, ∀ p ∈ P i, θ p = 1 - ρ ^ a i) (u : ℕ) :
    (∏ i ∈ I, representedBandTerm (P i) (S i) u (a i) ρ) =
      (∏ i ∈ I, ρ ^ (a i * ((S i).card - 1))) *
        markedWeightedResidual (I.biUnion P) (I.biUnion S) θ u := by
  classical
  have hterms : (∏ i ∈ I, representedBandTerm (P i) (S i) u (a i) ρ) =
      (∏ i ∈ I, ρ ^ (a i * ((S i).card - 1))) *
        ∏ i ∈ I, markedWeightedResidual (P i) (S i) θ u := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i hi =>
      representedBandTerm_eq_weightedResidual (P i) (S i) u (a i) ρ θ (hθ i hi))
  rw [hterms]
  congr 1
  by_cases hs : ∀ i ∈ I, S i ⊆ activeDivisors (P i) u
  · rw [markedWeightedResidual, ite_eq_left ((selected_union_active_iff I P S hS u).mpr hs),
      disjoint_bands_residual_union I P S hdis hS]
    have hd : Set.PairwiseDisjoint (↑I) (fun i => P i \ S i) := by
      intro i hi j hj hij
      exact (hdis hi hj hij).mono Finset.sdiff_subset Finset.sdiff_subset
    rw [Finset.prod_biUnion hd]
    apply Finset.prod_congr rfl
    intro i hi
    rw [markedWeightedResidual, ite_eq_left (hs i hi)]
  · rw [markedWeightedResidual, ite_eq_right (fun h => hs
      ((selected_union_active_iff I P S hS u).mp h))]
    push Not at hs
    obtain ⟨i, hi, his⟩ := hs
    exact Finset.prod_eq_zero hi (by simp [markedWeightedResidual, his])

/-- The single damping function attached to a disjoint collection of bands. -/
noncomputable def representedArrayDamping {ι : Type*} (I : Finset ι)
    (P : ι → Finset ℕ) (a : ι → ℕ) (ρ : ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ I, if p ∈ P i then 1 - ρ ^ a i else 0

theorem representedArrayDamping_on_band {ι : Type*} (I : Finset ι)
    (P : ι → Finset ℕ) (a : ι → ℕ) (ρ : ℝ)
    (hdis : Set.PairwiseDisjoint (↑I) P) {i : ι} (hi : i ∈ I)
    {p : ℕ} (hp : p ∈ P i) :
    representedArrayDamping I P a ρ p = 1 - ρ ^ a i := by
  classical
  unfold representedArrayDamping
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hp
  · intro j hj hji
    exact ite_eq_right (fun hpj => Finset.disjoint_left.mp (hdis hj hi hji) hpj hp)
  · exact fun h => (h hi).elim

theorem representedArrayDamping_mem_unitInterval {ι : Type*} (I : Finset ι)
    (P : ι → Finset ℕ) (a : ι → ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hdis : Set.PairwiseDisjoint (↑I) P) {p : ℕ} (hp : p ∈ I.biUnion P) :
    0 ≤ representedArrayDamping I P a ρ p ∧ representedArrayDamping I P a ρ p ≤ 1 := by
  obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
  rw [representedArrayDamping_on_band I P a ρ hdis hi hpi]
  exact ⟨sub_nonneg.mpr (pow_le_one₀ hρ hρ1), sub_le_self _ (pow_nonneg hρ _)⟩

/-- No damping-function existence hypothesis remains: the union function is
constructed directly from the bands and their multiplicities. -/
theorem represented_bands_eq_union_residual {ι : Type*} (I : Finset ι)
    (P S : ι → Finset ℕ) (a : ι → ℕ) (ρ : ℝ)
    (hdis : Set.PairwiseDisjoint (↑I) P) (hS : ∀ i ∈ I, S i ⊆ P i) (u : ℕ) :
    (∏ i ∈ I, representedBandTerm (P i) (S i) u (a i) ρ) =
      (∏ i ∈ I, ρ ^ (a i * ((S i).card - 1))) *
        markedWeightedResidual (I.biUnion P) (I.biUnion S)
          (representedArrayDamping I P a ρ) u :=
  represented_bands_eq_single_residual I P S a ρ _ hdis hS
    (fun _ hi _ hp => representedArrayDamping_on_band I P a ρ hdis hi hp) u

/-- In the single- and double-array expansions these are exactly the two
primewise Bonferroni parameters, including repeated selected primes. -/
theorem representedArrayDamping_one_or_two {ι : Type*} (I : Finset ι)
    (P : ι → Finset ℕ) (a : ι → ℕ) (hdis : Set.PairwiseDisjoint (↑I) P)
    (ha : ∀ i ∈ I, a i = 1 ∨ a i = 2) {p : ℕ} (hp : p ∈ I.biUnion P) :
    representedArrayDamping I P a (1 / 2) p = 1 / 2 ∨
      representedArrayDamping I P a (1 / 2) p = 3 / 4 := by
  obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
  rw [representedArrayDamping_on_band I P a (1 / 2) hdis hi hpi]
  rcases ha i hi with hai | hai <;> norm_num [hai]

end ArtinMatthews
