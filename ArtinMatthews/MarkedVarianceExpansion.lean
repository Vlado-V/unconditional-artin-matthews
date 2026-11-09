module

public import ArtinMatthews.MarkedEstimateVariance
public import ArtinMatthews.DivisorWeights


set_option backward.privateInPublic true
@[expose] public section

/-! Exact expansion of the nonnegative marking variance into its constant,
first-moment, and pair-moment terms. Diagonal pairs retain second moments. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable def markedArrayVarianceWeight {J I : Type*} [Fintype J] [Fintype I]
    [DecidableEq I] (P : J → I → Finset ℕ) (V : J → I → ℝ) (u : ℕ) : ℝ :=
  ((∑ j, divisorWeight Finset.univ (P j) (V j) u / independentArrayMean (P j) (V j)) /
    Fintype.card J - 1) ^ 2

theorem markedArrayVarianceWeight_nonneg {J I : Type*} [Fintype J] [Fintype I]
    [DecidableEq I] (P : J → I → Finset ℕ) (V : J → I → ℝ) (u : ℕ) :
    0 ≤ markedArrayVarianceWeight P V u := sq_nonneg _

/-- Algebraic variance expansion with the exact varying normalizers. -/
theorem marked_centered_average_expansion {J : Type*} [Fintype J]
    (w μ : J → ℝ) :
    ((∑ j, w j / μ j) / Fintype.card J - 1) ^ 2 =
      1 + (∑ j, (-2 / ((Fintype.card J : ℝ) * μ j)) * w j) +
        ∑ j, ∑ k, (1 / ((Fintype.card J : ℝ) ^ 2 * μ j * μ k)) * (w j * w k) := by
  have hlinear : (∑ j, (-2 / ((Fintype.card J : ℝ) * μ j)) * w j) =
      (-2 / (Fintype.card J : ℝ)) * ∑ j, w j / μ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hquadratic : (∑ j, ∑ k, (1 / ((Fintype.card J : ℝ) ^ 2 * μ j * μ k)) * (w j * w k)) =
      (1 / (Fintype.card J : ℝ) ^ 2) * (∑ j, w j / μ j) ^ 2 := by
    simp only [pow_two]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hlinear, hquadratic]
  ring

noncomputable def markedVariancePairModel {J : Type*} [DecidableEq J]
    (μ ν : J → ℝ) (j k : J) : ℝ := if j = k then ν j else μ j * μ k

/-- The off-diagonal model consists of independent first moments; the
resulting centered model is exactly the sum of normalized variances. -/
theorem marked_centered_model_expansion {J : Type*} [Fintype J] [DecidableEq J]
    (μ ν : J → ℝ) (hμ : ∀ j, μ j ≠ 0) (hJ : 0 < Fintype.card J) :
    1 + (∑ j, (-2 / ((Fintype.card J : ℝ) * μ j)) * μ j) +
      (∑ j, ∑ k, (1 / ((Fintype.card J : ℝ) ^ 2 * μ j * μ k)) * markedVariancePairModel μ ν j k) =
      (∑ j, (ν j / μ j ^ 2 - 1)) / (Fintype.card J : ℝ) ^ 2 := by
  classical
  have hpair (j k : J) : markedVariancePairModel μ ν j k / (μ j * μ k) =
      1 + if j = k then ν j / μ j ^ 2 - 1 else 0 := by
    by_cases hjk : j = k
    · subst k
      simp [markedVariancePairModel, pow_two]
    · simp only [markedVariancePairModel, ite_eq_right hjk, div_self (mul_ne_zero (hμ j) (hμ k)), add_zero]
  have hsum : (∑ j, ∑ k, markedVariancePairModel μ ν j k / (μ j * μ k)) =
      (Fintype.card J : ℝ) ^ 2 + ∑ j, (ν j / μ j ^ 2 - 1) := by
    simp_rw [hpair, Finset.sum_add_distrib]
    simp [pow_two]
  have hlinear : (∑ j, (-2 / ((Fintype.card J : ℝ) * μ j)) * μ j) = -2 := by
    have hb : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
    calc
      _ = ∑ _j : J, -2 / (Fintype.card J : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        field_simp [hμ j]
      _ = -2 := by simp; field_simp
  have hquad : (∑ j, ∑ k, (1 / ((Fintype.card J : ℝ) ^ 2 * μ j * μ k)) * markedVariancePairModel μ ν j k) =
      (∑ j, ∑ k, markedVariancePairModel μ ν j k / (μ j * μ k)) / (Fintype.card J : ℝ) ^ 2 := by
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hlinear, hquad, hsum]
  have hb : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  field_simp
  ring

end ArtinMatthews
