module

public import ArtinMatthews.GiantSamplingLargeSquareCount


set_option backward.privateInPublic true
@[expose] public section

/-! The two elementary sums of the actual small squarepart parameters. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem giantSampling_quarter_difference {d : ℕ} (hd : 0 < d) :
    (d : ℝ) ^ (-(3 / 4) : ℝ) ≤
      4 * ((d : ℝ) ^ (1 / 4 : ℝ) - ((d - 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) := by
  let u := (d : ℝ) ^ (1 / 4 : ℝ)
  let v := ((d - 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)
  have hd₀ : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hu : 0 < u := Real.rpow_pos_of_pos hd₀ _
  have hv : 0 ≤ v := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hvu : v ≤ u := Real.rpow_le_rpow (Nat.cast_nonneg _)
    (Nat.cast_le.mpr (Nat.sub_le d 1)) (by norm_num)
  have hu₄ : u ^ 4 = (d : ℝ) := by
    dsimp only [u]
    rw [← Real.rpow_mul_natCast hd₀.le]
    norm_num
  have hv₄ : v ^ 4 = ((d - 1 : ℕ) : ℝ) := by
    dsimp only [v]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  have hdiff : 1 = (u - v) * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) := by
    calc
      _ = (d : ℝ) - ((d - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hd, Nat.cast_one]
        ring
      _ = u ^ 4 - v ^ 4 := by rw [hu₄, hv₄]
      _ = _ := by ring
  have hsum : u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3 ≤ 4 * u ^ 3 := by
    have h₁ := mul_le_mul_of_nonneg_left hvu (sq_nonneg u)
    have h₂ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv hvu 2) hu.le
    have h₃ := pow_le_pow_left₀ hv hvu 3
    nlinarith
  have hmain := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hvu)
  rw [← hdiff] at hmain
  have hinv : (d : ℝ) ^ (-(3 / 4) : ℝ) = (u ^ 3)⁻¹ := by
    dsimp only [u]
    rw [← Real.rpow_mul_natCast hd₀.le, Real.rpow_neg hd₀.le]
    norm_num
  rw [hinv, ← one_div (u ^ 3)]
  apply (div_le_iff₀ (pow_pos hu 3)).mpr
  calc
    _ ≤ (u - v) * (4 * u ^ 3) := hmain
    _ = _ := by ring

theorem giantSampling_sum_quarter_differences (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
      ((d : ℝ) ^ (1 / 4 : ℝ) - ((d - 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ))) =
      (N : ℝ) ^ (1 / 4 : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert (by simp), ih, Nat.add_sub_cancel]
    ring

theorem giantSampling_smallSquare_power_sums (B : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    let P := (Finset.Icc 1 B).filter (fun d : ℕ => (d : ℝ) ≤ D)
    (∑ d ∈ P, (d : ℝ)) ≤ D ^ 2 ∧
      (∑ d ∈ P, (d : ℝ) ^ (-(3 / 4) : ℝ)) ≤ 4 * D ^ (1 / 4 : ℝ) := by
  let P := (Finset.Icc 1 B).filter (fun d : ℕ => (d : ℝ) ≤ D)
  have hpos (d : ℕ) (hd : d ∈ P) : 0 < d :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  have hle (d : ℕ) (hd : d ∈ P) : (d : ℝ) ≤ D := (Finset.mem_filter.mp hd).2
  have hcard : (P.card : ℝ) ≤ D :=
    giantSampling_positive_card_le P hD (fun d hd => ⟨hpos d hd, hle d hd⟩)
  have hsub : P ⊆ Finset.Icc 1 ⌊D⌋₊ := fun d hd =>
    Finset.mem_Icc.mpr ⟨hpos d hd, Nat.le_floor (hle d hd)⟩
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ ∑ _d ∈ P, D := Finset.sum_le_sum hle
      _ = (P.card : ℝ) * D := by simp
      _ ≤ D * D := mul_le_mul_of_nonneg_right hcard hD
      _ = _ := by ring
  · calc
      _ ≤ ∑ d ∈ Finset.Icc 1 ⌊D⌋₊, (d : ℝ) ^ (-(3 / 4) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ ∑ d ∈ Finset.Icc 1 ⌊D⌋₊,
          4 * ((d : ℝ) ^ (1 / 4 : ℝ) - ((d - 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) :=
        Finset.sum_le_sum (fun d hd => giantSampling_quarter_difference (Finset.mem_Icc.mp hd).1)
      _ = 4 * (⌊D⌋₊ : ℝ) ^ (1 / 4 : ℝ) := by
        rw [← Finset.mul_sum, giantSampling_sum_quarter_differences]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (Nat.floor_le hD) (by norm_num)) (by norm_num)

theorem giantSampling_squarepart_rpow_scales {T d : ℝ} (hT : 0 < T) (hd : 0 < d) :
    (T / d ^ 2) ^ (-(1 / 2) : ℝ) = T ^ (-(1 / 2) : ℝ) * d ∧
      (2 * T / d ^ 2) ^ (3 / 8 : ℝ) = (2 * T) ^ (3 / 8 : ℝ) * d ^ (-(3 / 4) : ℝ) := by
  constructor
  · rw [Real.div_rpow hT.le (sq_nonneg _) _, ← Real.rpow_natCast_mul hd.le]
    norm_num [Real.rpow_neg_one, div_inv_eq_mul]
  · rw [Real.div_rpow (by positivity) (sq_nonneg _) _, ← Real.rpow_natCast_mul hd.le,
      Real.rpow_neg hd.le, div_eq_mul_inv]
    norm_num

end ArtinMatthews
