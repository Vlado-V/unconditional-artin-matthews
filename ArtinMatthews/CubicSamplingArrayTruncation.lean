module

public import ArtinMatthews.MarkedArrayCoefficientMass
public import ArtinMatthews.MarkedProgressionWeightedPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! The Section 6.3 truncation keeps the represented tuple, its selected
prime union, and the actual prime-dependent damping. The retained depth is
arbitrary, so the literal source floor does not need a parity adjustment. -/

noncomputable section
namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

theorem cubicSampling_weightedTruncation_abs_error (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (k u : ℕ) :
    |markedWeightedResidual P S θ u - markedWeightedTruncation P S θ k u| ≤
      markedWeightedTail P S θ (k + 1) u := by
  let m := k / 2
  have hparity : k = 2 * m ∨ k = 2 * m + 1 := by dsimp only [m]; omega
  rcases hparity with heven | hodd
  · rw [heven, abs_sub_comm]
    obtain ⟨h₁, h₂⟩ := markedWeightedTruncation_error P S hP hS θ hθ m u
    rw [abs_of_nonneg h₁]
    exact h₂
  · rw [hodd, markedWeightedTruncation_eq P S hP hS, markedWeightedTail_eq P S hP hS]
    unfold markedWeightedResidual
    by_cases hs : S ⊆ activeDivisors P u
    · simp only [ite_eq_left hs]
      let g := markedWeightedInput u θ
      have hb (p : ℕ) (hp : p ∈ P \ S) : 0 ≤ g p ∧ g p ≤ 1 := by
        have hp' := hθ p (Finset.mem_sdiff.mp hp).1
        dsimp only [g, markedWeightedInput]
        split_ifs <;> simp_all
      have hlo := (BonferroniDensity.densityPolynomial_bounds (P \ S) g
        (fun p hp => (hb p hp).1) (fun p hp => (hb p hp).2) m).1
      have hhi := (BonferroniDensity.densityPolynomial_bounds (P \ S) g
        (fun p hp => (hb p hp).1) (fun p hp => (hb p hp).2) (m + 1)).2
      have hsucc : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      have hsign : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := by
        rw [← hsucc, pow_mul]
        norm_num
      rw [hsucc, BonferroniDensity.densityPolynomial_succ, hsign, one_mul] at hhi
      change |(∏ p ∈ P \ S, (1 - g p)) -
        BonferroniDensity.densityPolynomial (2 * m + 1) (P \ S) g| ≤ _
      rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
      linarith
    · simp only [ite_eq_right hs, sub_zero, abs_zero, le_refl]

theorem cubicSampling_selected_subset {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (a : J → ℕ) {t : (j : J) → Fin (a j) → ℕ}
    (ht : t ∈ representedArrayChoices P a) :
    representedArraySelected t ⊆ Finset.univ.biUnion P := by
  classical
  intro p hp
  obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
  have htj := Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp ht j)
  exact Finset.mem_biUnion.mpr ⟨j, hj, representedChoiceSet_subset htj hpj⟩

theorem cubicSampling_selected_card_le {J : Type*} [Fintype J] {a : J → ℕ}
    (t : (j : J) → Fin (a j) → ℕ) : (representedArraySelected t).card ≤ ∑ j, a j := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro j _hj
  exact Finset.card_image_le.trans_eq (by simp)

theorem cubicSampling_arrayDamping_bounds {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (a : J → ℕ) (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {p : ℕ} (hp : p ∈ Finset.univ.biUnion P) :
    0 ≤ representedArrayDamping Finset.univ P a (1 / 2) p ∧
      representedArrayDamping Finset.univ P a (1 / 2) p ≤ 1 :=
  representedArrayDamping_mem_unitInterval Finset.univ P a (by norm_num) (by norm_num)
    (fun _i _hi _j _hj hij => hdis hij) hp

def cubicSamplingArrayTruncation {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (a : J → ℕ) (k u : ℕ) : ℝ :=
  ∑ t ∈ representedArrayChoices P a, representedArrayCoefficient V a t *
    markedWeightedTruncation (Finset.univ.biUnion P) (representedArraySelected t)
      (representedArrayDamping Finset.univ P a (1 / 2)) k u

def cubicSamplingArrayTail {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (a : J → ℕ) (h u : ℕ) : ℝ :=
  ∑ t ∈ representedArrayChoices P a, representedArrayCoefficient V a t *
    markedWeightedTail (Finset.univ.biUnion P) (representedArraySelected t)
      (representedArrayDamping Finset.univ P a (1 / 2)) h u

theorem cubicSampling_arrayTruncation_error {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (a : J → ℕ) (ha : ∀ j, 0 < a j)
    (hV : ∀ j, 0 ≤ V j) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (k u : ℕ) :
    |(∏ j, (bandWeight (P j) (V j) u) ^ a j) - cubicSamplingArrayTruncation P V a k u| ≤
      cubicSamplingArrayTail P V a (k + 1) u := by
  let U := Finset.univ.biUnion P
  let θ := representedArrayDamping Finset.univ P a (1 / 2)
  have hU (p : ℕ) (hp : p ∈ U) : p.Prime := by
    obtain ⟨j, _hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hP j p hpj
  rw [bandWeight_product_powers_eq_normalized_residual_sum P V a ha hdis,
    cubicSamplingArrayTruncation, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient V a t *
        (markedWeightedResidual U (representedArraySelected t) θ u -
          markedWeightedTruncation U (representedArraySelected t) θ k u)| := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le (representedArrayChoices P a) (fun t => representedArrayCoefficient V a t *
          (markedWeightedResidual U (representedArraySelected t) θ u -
            markedWeightedTruncation U (representedArraySelected t) θ k u))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      have hc := representedArrayCoefficient_nonneg_for_mass V a hV t
      rw [abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left
        (cubicSampling_weightedTruncation_abs_error U (representedArraySelected t) hU
          (cubicSampling_selected_subset P a ht) θ
          (fun _ hp => cubicSampling_arrayDamping_bounds P a hdis hp) k u) hc

theorem cubicSampling_arrayTruncation_eq_divisors {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (a : J → ℕ) (k u : ℕ) :
    cubicSamplingArrayTruncation P V a k u =
      ∑ t ∈ representedArrayChoices P a,
        ∑ i ∈ markedWeightedIndices (Finset.univ.biUnion P) (representedArraySelected t) k,
          if markedWeightedDivisor (representedArraySelected t) i ∣ u then
            representedArrayCoefficient V a t *
              markedWeightedCoefficient (representedArrayDamping Finset.univ P a (1 / 2)) i
          else 0 := by
  unfold cubicSamplingArrayTruncation
  apply Finset.sum_congr rfl
  intro t _ht
  rw [markedWeightedTruncation_eq_polynomial, markedIndexedDivisorPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  split_ifs <;> simp

end ArtinMatthews
