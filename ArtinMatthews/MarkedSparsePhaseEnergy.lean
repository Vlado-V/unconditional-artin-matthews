module

public import ArtinMatthews.MarkedSparsePhaseKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Normalized coefficient mass and energy for the actual integer interval
polynomial. Together with the proved logarithmic-phase row estimate, this
supplies the second sparse-frequency estimate. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable section

theorem markedDyadicPolynomial_coefficient_mass (L R : ℕ) (U M : ℝ)
    (hU : 1 ≤ U) (hR : (R:ℝ) ≤ 2*U) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Icc L R, ‖a n‖ ≤ M) :
    (∑ n ∈ Finset.Icc L R, ‖a n / U‖^2) ≤ 3*M^2/U := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hc : ((Finset.Icc L R).card:ℝ) ≤ 3*U := by
    have hh : (Finset.Icc L R).card ≤ R+1 := by rw [Nat.card_Icc]; omega
    have hhR : ((Finset.Icc L R).card:ℝ) ≤ (R:ℝ)+1 := by exact_mod_cast hh
    linarith
  calc
    _ ≤ ∑ _n ∈ Finset.Icc L R, (M/U)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply pow_le_pow_left₀ (norm_nonneg _)
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hU0]
      exact div_le_div_of_nonneg_right (ha n hn) hU0.le
    _ = ((Finset.Icc L R).card:ℝ)*(M/U)^2 := by simp
    _ ≤ (3*U)*(M/U)^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by field_simp

theorem markedDyadicPolynomial_energy_from_rows (L R : ℕ) (U A M T : ℝ)
    (hU : 1 ≤ U) (hR : (R:ℝ) ≤ 2*U) (hA : 0 ≤ A)
    (hT : 0 ≤ T) (a : ℕ → ℂ) (S : Finset ℝ)
    (ha : ∀ n ∈ Finset.Icc L R, ‖a n‖ ≤ M)
    (hrow : ∀ t ∈ S, ∑ u ∈ S, ‖markedLogKernel L R (t-u)‖ ≤
      A*U*(3+2*Real.log (T+1))) :
    (∑ t ∈ S, ‖markedDyadicPolynomial L R U a t‖^2) ≤
      3*A*(3+2*Real.log (T+1))*M^2 := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hlog : 0 ≤ Real.log (T+1) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ A*U*(3+2*Real.log (T+1)) := by positivity
  calc
    _ ≤ (A*U*(3+2*Real.log (T+1)))*
        ∑ n ∈ Finset.Icc L R, ‖a n/U‖^2 :=
      markedDyadicPolynomial_sparse_energy L R U a S hB hrow
    _ ≤ (A*U*(3+2*Real.log (T+1)))*(3*M^2/U) :=
      mul_le_mul_of_nonneg_left
        (markedDyadicPolynomial_coefficient_mass L R U M hU hR a ha) hB
    _ = _ := by field_simp

end
end ArtinMatthews
