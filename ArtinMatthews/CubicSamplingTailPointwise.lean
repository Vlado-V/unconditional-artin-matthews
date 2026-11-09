module

public import ArtinMatthews.CubicSamplingArrayTruncation


set_option backward.privateInPublic true
@[expose] public section

/-! A positive omitted layer is supported on actual hits, including the
represented labels. This produces the pointwise binomial majorant used for
its square mean. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

private theorem cubicSampling_weightedTail_le_choose (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (h u : ℕ) :
    markedWeightedTail P S θ h u ≤ ((bandCount P u).choose h : ℝ) := by
  let T := (P \ S).powersetCard h
  let A := (activeDivisors P u).powersetCard h
  let D := T.filter (fun Q => (∏ p ∈ S ∪ Q, p) ∣ u)
  have hsub : D ⊆ A := by
    intro Q hQ
    obtain ⟨hQT, hd⟩ := Finset.mem_filter.mp hQ
    obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp hQT
    have hprime (p : ℕ) (hp : p ∈ S ∪ Q) : p.Prime :=
      hP p ((Finset.mem_union.mp hp).elim (fun hp => hS hp)
        (fun hp => (Finset.mem_sdiff.mp (hsub hp)).1))
    have hall := (marked_prime_product_dvd_iff (S ∪ Q) hprime u).mp hd
    exact Finset.mem_powersetCard.mpr ⟨fun p hp => Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp (hsub hp)).1, hall p (Finset.mem_union_right _ hp)⟩, hc⟩
  unfold markedWeightedTail markedIndexedDivisorPolynomial
  rw [← Finset.sum_filter]
  change (∑ Q ∈ D, ∏ p ∈ Q, θ p) ≤ _
  calc
    _ ≤ ∑ _Q ∈ D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro Q hQ
      have hs := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hQ).1).1
      exact Finset.prod_le_one₀ (fun p hp => (hθ p (Finset.mem_sdiff.mp (hs hp)).1).1)
        (fun p hp => (hθ p (Finset.mem_sdiff.mp (hs hp)).1).2)
    _ ≤ ∑ _Q ∈ A, (1 : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le_one)
    _ = _ := by
      simp only [A, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_one, bandCount]

private theorem cubicSampling_array_coefficient_le {J : Type*} [Fintype J]
    (V : J → ℝ) (a : J → ℕ) {v : ℝ} (hv : 0 < v) (hV : ∀ j, v ≤ V j)
    (t : (j : J) → Fin (a j) → ℕ) :
    representedArrayCoefficient V a t ≤ (1 / v) ^ (∑ j, a j) := by
  have hden : v ^ (∑ j, a j) ≤ ∏ j, V j ^ a j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => pow_nonneg hv.le _)
      (fun j _ => pow_le_pow_left₀ hv.le (hV j) _)
  have hnum : (∏ j, (1 / 2 : ℝ) ^ (a j * ((representedChoiceSet (t j)).card - 1))) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => pow_nonneg (by norm_num) _)
      (fun _ _ => pow_le_one₀ (by norm_num) (by norm_num))
  unfold representedArrayCoefficient
  calc
    _ ≤ 1 / v ^ (∑ j, a j) := div_le_div₀ zero_le_one hnum (pow_pos hv _) hden
    _ = _ := by rw [div_pow, one_pow]

theorem cubicSampling_arrayTail_le_binomial {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (a : J → ℕ) {v : ℝ} (hv : 0 < v)
    (hV : ∀ j, v ≤ V j) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (h u : ℕ) :
    cubicSamplingArrayTail P V a h u ≤
      (1 / v) ^ (∑ j, a j) *
        (bandCount (Finset.univ.biUnion P) u : ℝ) ^ (∑ j, a j) *
          ((bandCount (Finset.univ.biUnion P) u).choose h : ℝ) := by
  classical
  let U := Finset.univ.biUnion P
  let θ := representedArrayDamping Finset.univ P a (1 / 2)
  let A := activeDivisors U u
  let B := (representedArrayChoices P a).filter (fun t => representedArraySelected t ⊆ A)
  let K := ∑ j, a j
  let C := (1 / v) ^ K
  let F (t : (j : J) → Fin (a j) → ℕ) :=
    representedArrayCoefficient V a t * markedWeightedTail U (representedArraySelected t) θ h u
  have hU (p : ℕ) (hp : p ∈ U) : p.Prime := by
    obtain ⟨j, _hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hP j p hpj
  have hBsub : B ⊆ representedArrayChoices (fun _ => A) a := by
    intro t ht
    obtain ⟨_ht, hsel⟩ := Finset.mem_filter.mp ht
    apply Fintype.mem_piFinset.mpr
    intro j
    apply Fintype.mem_piFinset.mpr
    intro i
    apply hsel
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hcard : B.card ≤ A.card ^ K := by
    apply (Finset.card_le_card hBsub).trans_eq
    simp only [representedArrayChoices, Fintype.card_piFinset, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, K, Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ t ∈ B, F t) = ∑ t ∈ representedArrayChoices P a, F t := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t ht htB
    have hs : ¬ representedArraySelected t ⊆ A :=
      fun hh => htB (Finset.mem_filter.mpr ⟨ht, hh⟩)
    dsimp only [F]
    rw [markedWeightedTail_eq U (representedArraySelected t) hU
      (cubicSampling_selected_subset P a ht), ite_eq_right hs, mul_zero]
  change (∑ t ∈ representedArrayChoices P a, F t) ≤
    C * (A.card : ℝ) ^ K * (A.card.choose h : ℝ)
  rw [← hsum]
  calc
    _ ≤ ∑ _t ∈ B, C * (A.card.choose h : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      have hsel := cubicSampling_selected_subset P a (Finset.mem_filter.mp ht).1
      have hc := representedArrayCoefficient_nonneg_for_mass V a (fun j => hv.le.trans (hV j)) t
      exact (mul_le_mul_of_nonneg_left
        (cubicSampling_weightedTail_le_choose U (representedArraySelected t) hU hsel θ
          (fun _ hp => cubicSampling_arrayDamping_bounds P a hdis hp) h u) hc).trans
        (mul_le_mul_of_nonneg_right (cubicSampling_array_coefficient_le V a hv hV t)
          (Nat.cast_nonneg _))
    _ = (B.card : ℝ) * (C * (A.card.choose h : ℝ)) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A.card : ℝ) ^ K * (C * (A.card.choose h : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by dsimp only [C]; positivity)
    _ = _ := by ring

end ArtinMatthews
