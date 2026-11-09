module

public import ArtinMatthews.GiantOrderedProductMoment


set_option backward.privateInPublic true
@[expose] public section

/-! The exact divisor fourth-moment budget in Section 6.3. The final
factor is counted by a floor, giving fifteen harmonic factors. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

private theorem giant_ordered_product_succ_count_le (k X : ℕ) :
    ((giantOrderedProductTuples (k + 1) X).card : ℝ) ≤
      (X : ℝ) * (1 + Real.log (X : ℝ)) ^ k := by
  let A := Fintype.piFinset (fun _ : Fin k => Finset.Ioc 0 X)
  let S := A.sigma (fun t => Finset.Ioc 0 (X / ∏ i, t i))
  let f (t : Fin (k + 1) → ℕ) : Σ _ : Fin k → ℕ, ℕ := ⟨Fin.tail t, t 0⟩
  have hcard : (giantOrderedProductTuples (k + 1) X).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn f
    · intro t ht
      obtain ⟨htpos, hprod⟩ := mem_giantOrderedProductTuples.mp ht
      have hpos : 0 < ∏ i, t i := Finset.prod_pos (fun i _ => htpos i)
      have hbound (i : Fin (k + 1)) : t i ≤ X :=
        (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem t (Finset.mem_univ i))).trans hprod
      have htail : Fin.tail t ∈ A := Fintype.mem_piFinset.mpr fun i =>
        Finset.mem_Ioc.mpr ⟨htpos i.succ, hbound i.succ⟩
      have htailpos : 0 < ∏ i, Fin.tail t i := Finset.prod_pos (fun i _ => htpos i.succ)
      have hhead : t 0 ≤ X / ∏ i, Fin.tail t i :=
        (Nat.le_div_iff_mul_le htailpos).mpr ((Fin.prod_univ_succ t).symm.trans_le hprod)
      exact Finset.mem_sigma.mpr ⟨htail, Finset.mem_Ioc.mpr ⟨htpos 0, hhead⟩⟩
    · intro t _ht u _hu he
      have h := congrArg (fun p : Σ _ : Fin k → ℕ, ℕ =>
        Fin.cons (α := fun _ : Fin (k + 1) => ℕ) p.2 p.1) he
      simpa only [f, Fin.cons_self_tail] using h
  have hharm : (∑ a ∈ Finset.Ioc 0 X, (a : ℝ)⁻¹) ≤ 1 + Real.log (X : ℝ) := by
    have he : Finset.Ioc 0 X = Finset.Icc 1 X := by
      ext a
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [he]
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
      harmonic_le_one_add_log X
  calc
    _ ≤ (S.card : ℝ) := Nat.cast_le.mpr hcard
    _ = ∑ t ∈ A, ((X / ∏ i, t i : ℕ) : ℝ) := by
      simp only [S, Finset.card_sigma, Nat.card_Ioc, Nat.sub_zero, Nat.cast_sum]
    _ ≤ ∑ t ∈ A, (X : ℝ) * ∏ i, (t i : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro t _ht
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod, ← div_eq_mul_inv]
      exact Nat.cast_div_le
    _ = (X : ℝ) * (∑ a ∈ Finset.Ioc 0 X, (a : ℝ)⁻¹) ^ k := by
      rw [← Finset.mul_sum, ← Finset.prod_univ_sum (fun _ : Fin k => Finset.Ioc 0 X)
        (fun _ a => (a : ℝ)⁻¹)]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hharm k) (Nat.cast_nonneg _)

private theorem cubicSampling_divisorCard_le_tuple_two (n : ℕ) :
    n.divisors.card ≤ (giantOrderedProductFiber 2 n).card := by
  let f (d : ℕ) : Fin 2 → ℕ := ![d, n / d]
  apply Finset.card_le_card_of_injOn f
  · intro d hd
    obtain ⟨hdvd, hn⟩ := Nat.mem_divisors.mp hd
    have hdp : 0 < d := by
      apply Nat.pos_of_ne_zero
      intro h
      subst d
      exact hn (zero_dvd_iff.mp hdvd)
    have hq : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hdp
    apply mem_giantOrderedProductFiber.mpr
    constructor
    · intro i
      fin_cases i
      · exact hdp
      · exact hq
    · simp only [f, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact (Nat.mul_comm d (n / d)).trans (Nat.div_mul_cancel hdvd)
  · intro d _hd e _he h
    exact congrFun h 0

theorem cubicSampling_divisor_fourth_moment (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X, (n.divisors.card : ℝ) ^ 4) ≤
      (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 15 := by
  have hrow (n : ℕ) : n.divisors.card ^ 4 ≤ (giantOrderedProductFiber 16 n).card := by
    calc
      _ = (n.divisors.card ^ 2) ^ 2 := by rw [← pow_mul]
      _ ≤ ((giantOrderedProductFiber 4 n).card) ^ 2 := Nat.pow_le_pow_left
        ((Nat.pow_le_pow_left (cubicSampling_divisorCard_le_tuple_two n) 2).trans
          (giant_ordered_product_fiber_square_le 2 n)) _
      _ ≤ _ := giant_ordered_product_fiber_square_le 4 n
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 X, ((giantOrderedProductFiber 16 n).card : ℝ) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact_mod_cast hrow n
    _ = ((giantOrderedProductTuples 16 X).card : ℝ) := giant_ordered_product_fiber_card_sum 16 X
    _ ≤ _ := giant_ordered_product_succ_count_le 15 X

theorem cubicSampling_shifted_divisor_fourth_moment (N : ℕ) :
    (∑ u ∈ Finset.Icc 1 N, ((u + 1).divisors.card : ℝ) ^ 4) ≤
      ((N + 1 : ℕ) : ℝ) * (1 + Real.log ((N + 1 : ℕ) : ℝ)) ^ 15 := by
  have hsub : (Finset.Icc 1 N).image Nat.succ ⊆ Finset.Ioc 0 (N + 1) := by
    intro n hn
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ioc.mpr ⟨Nat.succ_pos _, Nat.succ_le_succ (Finset.mem_Icc.mp hu).2⟩
  calc
    _ = ∑ n ∈ (Finset.Icc 1 N).image Nat.succ, (n.divisors.card : ℝ) ^ 4 :=
      (Finset.sum_image Nat.succ_injective.injOn).symm
    _ ≤ ∑ n ∈ Finset.Ioc 0 (N + 1), (n.divisors.card : ℝ) ^ 4 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := cubicSampling_divisor_fourth_moment (N + 1)

end ArtinMatthews
