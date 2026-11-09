module

public import ArtinMatthews.MarkedEstimateDeweighting


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite averaging behind the removal of marking arrays. -/

namespace ArtinMatthews

open scoped BigOperators

theorem marked_average_sum_deviation {J U : Type*} [Fintype J]
    (S : Finset U) (a : U → ℂ) (z : J → U → ℝ) :
    (∑ u ∈ S, a u * (((∑ j, z j u) / Fintype.card J - 1 : ℝ) : ℂ)) =
      (∑ j, ∑ u ∈ S, a u * (z j u : ℂ)) / (Fintype.card J : ℂ) - ∑ u ∈ S, a u := by
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_sum,
    Complex.ofReal_natCast, Complex.ofReal_one, mul_sub, mul_one, Finset.sum_sub_distrib]
  simp_rw [← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
  rw [Finset.sum_comm]

theorem marked_average_norm_bound {J U : Type*} [Fintype J]
    (S : Finset U) (a : U → ℂ) (z : J → U → ℝ) (hJ : 0 < Fintype.card J) :
    ‖∑ u ∈ S, a u‖ ≤ (∑ j, ‖∑ u ∈ S, a u * (z j u : ℂ)‖) / Fintype.card J +
      ‖∑ u ∈ S, a u * (((∑ j, z j u) / Fintype.card J - 1 : ℝ) : ℂ)‖ := by
  have hb : (0 : ℝ) < Fintype.card J := by exact_mod_cast hJ
  have heq : (∑ u ∈ S, a u) =
      (∑ j, ∑ u ∈ S, a u * (z j u : ℂ)) / (Fintype.card J : ℂ) -
        (∑ u ∈ S, a u * (((∑ j, z j u) / Fintype.card J - 1 : ℝ) : ℂ)) := by
    rw [marked_average_sum_deviation]
    ring
  calc
    _ ≤ ‖(∑ j, ∑ u ∈ S, a u * (z j u : ℂ)) / (Fintype.card J : ℂ)‖ +
        ‖∑ u ∈ S, a u * (((∑ j, z j u) / Fintype.card J - 1 : ℝ) : ℂ)‖ := by
      rw [heq]
      exact norm_sub_le _ _
    _ = ‖∑ j, ∑ u ∈ S, a u * (z j u : ℂ)‖ / Fintype.card J +
        ‖∑ u ∈ S, a u * (((∑ j, z j u) / Fintype.card J - 1 : ℝ) : ℂ)‖ := by
      simp only [norm_div, Complex.norm_natCast]
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right (norm_sum_le _ _) hb.le) le_rfl

theorem marked_scaled_average_bound {J U : Type*} [Fintype J]
    (S : Finset U) (a : U → ℂ) (z : J → U → ℝ) (hJ : 0 < Fintype.card J)
    {s M D : ℝ} (hs : 0 ≤ s)
    (hM : ∀ j, s * ‖∑ u ∈ S, a u * (z j u : ℂ)‖ ≤ M)
    (hD : s * ‖∑ u ∈ S, a u * (((∑ j, z j u) / Fintype.card J - 1 : ℝ) : ℂ)‖ ≤ D) :
    s * ‖∑ u ∈ S, a u‖ ≤ M + D := by
  have hb : (0 : ℝ) < Fintype.card J := by exact_mod_cast hJ
  have havg : s * ((∑ j, ‖∑ u ∈ S, a u * (z j u : ℂ)‖) / Fintype.card J) ≤ M := by
    calc
      _ = (∑ j, s * ‖∑ u ∈ S, a u * (z j u : ℂ)‖) / Fintype.card J := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ (∑ _j : J, M) / Fintype.card J :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ => hM j)) hb.le
      _ = M := by simp; field_simp
  have h := mul_le_mul_of_nonneg_left (marked_average_norm_bound S a z hJ) hs
  rw [mul_add] at h
  linarith

end ArtinMatthews
