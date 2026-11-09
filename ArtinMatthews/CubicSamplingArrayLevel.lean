module

public import ArtinMatthews.CubicSamplingArrayTruncation
public import ArtinMatthews.RoughBonferroniDivisors


set_option backward.privateInPublic true
@[expose] public section

/-! Actual retained squarefree divisors and their absolute coefficient mass.
Repeated labels and coincident divisor values keep their indexed
multiplicities. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem cubicSampling_retainedDivisor_level {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (a : J → ℕ) {Z : ℝ} (hZ : 1 ≤ Z)
    (hP : ∀ j p, p ∈ P j → p.Prime ∧ (p : ℝ) ≤ Z)
    {t : (j : J) → Fin (a j) → ℕ} (ht : t ∈ representedArrayChoices P a)
    {k : ℕ} {i : MarkedWeightedIndex}
    (hi : i ∈ markedWeightedIndices (Finset.univ.biUnion P) (representedArraySelected t) k) :
    0 < markedWeightedDivisor (representedArraySelected t) i ∧
      Squarefree (markedWeightedDivisor (representedArraySelected t) i) ∧
      (markedWeightedDivisor (representedArraySelected t) i : ℝ) ≤ Z ^ (k + ∑ j, a j) := by
  let U := Finset.univ.biUnion P
  let S := representedArraySelected t
  let T := S ∪ i.2
  have hS : S ⊆ U := cubicSampling_selected_subset P a ht
  obtain ⟨hi₀, hi₁⟩ := Finset.mem_sigma.mp hi
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hi₁
  have hT : T ⊆ U := Finset.union_subset hS (fun _ hp => (Finset.mem_sdiff.mp (hsub hp)).1)
  have hp (p : ℕ) (hp : p ∈ T) : p.Prime ∧ (p : ℝ) ≤ Z := by
    obtain ⟨j, _hj, hbp⟩ := Finset.mem_biUnion.mp (hT hp)
    exact hP j p hbp
  have hcardT : T.card ≤ k + ∑ j, a j := by
    have h₁ : S.card ≤ ∑ j, a j := cubicSampling_selected_card_le t
    have h₂ := Finset.card_union_le S i.2
    have h₃ := Finset.mem_range.mp hi₀
    change T.card ≤ _ at h₂
    omega
  refine ⟨roughSubsetDivisor_pos T (fun p hm => (hp p hm).1),
    roughSubsetDivisor_squarefree T (fun p hm => (hp p hm).1), ?_⟩
  change ((∏ p ∈ T, p : ℕ) : ℝ) ≤ _
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _p ∈ T, Z := Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p)
      (fun p hm => (hp p hm).2)
    _ = Z ^ T.card := Finset.prod_const _
    _ ≤ _ := pow_le_pow_right₀ hZ hcardT

theorem cubicSampling_retainedCoefficient_mass {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (a : J → ℕ) {v Z : ℝ} (hv : 0 < v) (hZ : 1 ≤ Z)
    (hV : ∀ j, v ≤ V j) (hP : ∀ j p, p ∈ P j → p.Prime ∧ (p : ℝ) ≤ Z)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (k : ℕ) :
    (∑ t ∈ representedArrayChoices P a,
      ∑ i ∈ markedWeightedIndices (Finset.univ.biUnion P) (representedArraySelected t) k,
        |representedArrayCoefficient V a t *
          markedWeightedCoefficient (representedArrayDamping Finset.univ P a (1 / 2)) i|) ≤
      (Z / v) ^ (∑ j, a j) * ((k + 1 : ℕ) : ℝ) * Z ^ k := by
  let U := Finset.univ.biUnion P
  let θ := representedArrayDamping Finset.univ P a (1 / 2)
  have hU (p : ℕ) (hp : p ∈ U) : p.Prime ∧ (p : ℝ) ≤ Z := by
    obtain ⟨j, _hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hP j p hpj
  have hUcard := marked_prime_set_card_le U (fun p hp => (hU p hp).1)
    (zero_le_one.trans hZ) (fun p hp => (hU p hp).2)
  have hrow (S : Finset ℕ) :
      (∑ i ∈ markedWeightedIndices U S k, |markedWeightedCoefficient θ i|) ≤
        ((k + 1 : ℕ) : ℝ) * Z ^ k := by
    have hS : max 1 ((U \ S).card : ℝ) ≤ Z := max_le hZ
      ((Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)).trans hUcard)
    exact (markedWeightedCoefficient_mass_le U S θ
      (fun _ hp => cubicSampling_arrayDamping_bounds P a hdis hp) k).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hS k)
          (Nat.cast_nonneg _))
  have hc := representedArrayCoefficient_mass_le P V a hv (zero_le_one.trans hZ) hV
    (fun j => marked_prime_set_card_le (P j) (fun p hp => (hP j p hp).1)
      (zero_le_one.trans hZ) (fun p hp => (hP j p hp).2))
  simp_rw [abs_mul, ← Finset.mul_sum]
  calc
    _ ≤ ∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient V a t| *
        (((k + 1 : ℕ) : ℝ) * Z ^ k) := by
      apply Finset.sum_le_sum
      intro t _ht
      exact mul_le_mul_of_nonneg_left (hrow (representedArraySelected t)) (abs_nonneg _)
    _ = (∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient V a t|) *
        (((k + 1 : ℕ) : ℝ) * Z ^ k) := (Finset.sum_mul _ _ _).symm
    _ ≤ (Z / v) ^ (∑ j, a j) * (((k + 1 : ℕ) : ℝ) * Z ^ k) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [mul_assoc]

end ArtinMatthews
