module

public import ArtinMatthews.MarkedProgressionComparison


set_option backward.privateInPublic true
@[expose] public section

/-! Exact linear combination and triangle bounds for families of marked
progression sums. Signed coefficients and repeated represented unions are
both retained; no independence or injectivity hypothesis is used. -/

namespace ArtinMatthews

open scoped BigOperators

variable {ι : Type*}

/-- Exact linearity of the progression discrepancy in a finite family. -/
theorem marked_family_discrepancy_eq (U : Finset ℕ) (J : Finset ι)
    (w : ℕ → ℝ) (c M : ι → ℝ) (H : ι → ℕ → ℝ) (t : ℝ) :
    (∑ u ∈ U, w u * ∑ i ∈ J, c i * H i u) - t * (∑ i ∈ J, c i * M i) =
      ∑ i ∈ J, c i * ((∑ u ∈ U, w u * H i u) - t * M i) := by
  have hsum : (∑ u ∈ U, w u * ∑ i ∈ J, c i * H i u) =
      ∑ i ∈ J, c i * ∑ u ∈ U, w u * H i u := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Summed discrepancy is controlled by the sum of the individual errors
with the actual absolute coefficients. -/
theorem marked_family_summed_error_le (R : Finset ℕ) (U : ℕ → Finset ℕ) (J : Finset ι)
    (w : ℕ → ℝ) (c M : ι → ℝ) (H : ι → ℕ → ℝ) (t : ℕ → ℝ) :
    (∑ r ∈ R, |(∑ u ∈ U r, w u * ∑ i ∈ J, c i * H i u) -
      t r * (∑ i ∈ J, c i * M i)|) ≤
      ∑ i ∈ J, |c i| * ∑ r ∈ R, |(∑ u ∈ U r, w u * H i u) - t r * M i| := by
  calc
    _ = ∑ r ∈ R, |∑ i ∈ J, c i * ((∑ u ∈ U r, w u * H i u) - t r * M i)| := by
      apply Finset.sum_congr rfl
      intro r _
      rw [marked_family_discrepancy_eq]
    _ ≤ ∑ r ∈ R, ∑ i ∈ J, |c i * ((∑ u ∈ U r, w u * H i u) - t r * M i)| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      simp_rw [abs_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- A common rounding bound and reciprocal-weighted model bound remain
separate when summing represented choices. This separation is essential:
the number of choices is large, while their reciprocal mass is bounded. -/
theorem marked_family_summed_error_of_bounds (R : Finset ℕ) (U : ℕ → Finset ℕ)
    (J : Finset ι) (w : ℕ → ℝ) (c M : ι → ℝ) (H : ι → ℕ → ℝ) (t : ℕ → ℝ)
    (d : ι → ℝ) (B₀ B₁ : ℝ)
    (h : ∀ i ∈ J, (∑ r ∈ R, |(∑ u ∈ U r, w u * H i u) - t r * M i|) ≤
      B₀ + B₁ / d i) :
    (∑ r ∈ R, |(∑ u ∈ U r, w u * ∑ i ∈ J, c i * H i u) -
      t r * (∑ i ∈ J, c i * M i)|) ≤
      B₀ * (∑ i ∈ J, |c i|) + B₁ * (∑ i ∈ J, |c i| / d i) := by
  apply (marked_family_summed_error_le R U J w c M H t).trans
  calc
    _ ≤ ∑ i ∈ J, |c i| * (B₀ + B₁ / d i) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (h i hi) (abs_nonneg _))
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

end ArtinMatthews
