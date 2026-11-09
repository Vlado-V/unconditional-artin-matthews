module

public import ArtinMatthews.MarkedVarianceExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! A finite family representation of the actual marking variance with
explicitly bounded coefficients. Constant, linear, diagonal and off-diagonal
terms stay distinct throughout. -/

namespace ArtinMatthews

open scoped BigOperators

abbrev MarkedVarianceIndex (J : Type*) := Unit ⊕ (J ⊕ (J × J))

noncomputable def markedVarianceCoefficient {J : Type*} [Fintype J]
    (μ : J → ℝ) : MarkedVarianceIndex J → ℝ
  | .inl _ => 1
  | .inr (.inl j) => -2 / ((Fintype.card J : ℝ) * μ j)
  | .inr (.inr (j, k)) => 1 / ((Fintype.card J : ℝ) ^ 2 * μ j * μ k)

noncomputable def markedVarianceValue {J : Type*} (w : J → ℝ) : MarkedVarianceIndex J → ℝ
  | .inl _ => 1
  | .inr (.inl j) => w j
  | .inr (.inr (j, k)) => w j * w k

noncomputable def markedVarianceModel {J : Type*} [DecidableEq J]
    (μ ν : J → ℝ) : MarkedVarianceIndex J → ℝ
  | .inl _ => 1
  | .inr (.inl j) => μ j
  | .inr (.inr (j, k)) => markedVariancePairModel μ ν j k

theorem markedVarianceFamily_value {J : Type*} [Fintype J] (w μ : J → ℝ) :
    (∑ q, markedVarianceCoefficient μ q * markedVarianceValue w q) =
      ((∑ j, w j / μ j) / Fintype.card J - 1) ^ 2 := by
  rw [marked_centered_average_expansion]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, markedVarianceCoefficient,
    markedVarianceValue, mul_one, Fintype.sum_unique]
  ring

theorem markedVarianceFamily_model {J : Type*} [Fintype J] [DecidableEq J]
    (μ ν : J → ℝ) (hμ : ∀ j, μ j ≠ 0) (hJ : 0 < Fintype.card J) :
    (∑ q, markedVarianceCoefficient μ q * markedVarianceModel μ ν q) =
      (∑ j, (ν j / μ j ^ 2 - 1)) / (Fintype.card J : ℝ) ^ 2 := by
  rw [← marked_centered_model_expansion μ ν hμ hJ]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, markedVarianceCoefficient,
    markedVarianceModel, mul_one, Fintype.sum_unique]
  ring

/-- A lower bound on the true means controls every coefficient in the
variance expansion uniformly over the prime-band positions. -/
theorem markedVarianceCoefficient_bound {J : Type*} [Fintype J]
    (μ : J → ℝ) {v : ℝ} (hv : 0 < v) (hμ : ∀ j, v ≤ μ j)
    (hJ : 0 < Fintype.card J) (q : MarkedVarianceIndex J) :
    |markedVarianceCoefficient μ q| ≤ 1 + 2 / v + 1 / v ^ 2 := by
  have hb : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast hJ
  have hb0 : (0 : ℝ) < Fintype.card J := by positivity
  have hm (j : J) : 0 < μ j := hv.trans_le (hμ j)
  have htwo : 0 ≤ (2 : ℝ) / v := by positivity
  have hone : 0 ≤ (1 : ℝ) / v ^ 2 := by positivity
  rcases q with q | j | ⟨j, k⟩
  · simp only [markedVarianceCoefficient, abs_one]
    linarith
  · have hd : v ≤ (Fintype.card J : ℝ) * μ j := by
      nlinarith [hμ j, mul_le_mul_of_nonneg_right hb (hm j).le]
    have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hv hd
    simp only [markedVarianceCoefficient, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (mul_pos hb0 (hm j))]
    linarith
  · have hpair : v ^ 2 ≤ μ j * μ k := by
      have h := mul_le_mul (hμ j) (hμ k) hv.le (hm j).le
      nlinarith
    have hb2 : (1 : ℝ) ≤ (Fintype.card J : ℝ) ^ 2 := by nlinarith
    have hd : v ^ 2 ≤ (Fintype.card J : ℝ) ^ 2 * μ j * μ k := by
      nlinarith [mul_le_mul_of_nonneg_right hb2 (mul_pos (hm j) (hm k)).le]
    have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (sq_pos_of_pos hv) hd
    simp only [markedVarianceCoefficient, abs_div, abs_one,
      abs_of_pos (mul_pos (mul_pos (sq_pos_of_pos hb0) (hm j)) (hm k))]
    linarith

end ArtinMatthews
