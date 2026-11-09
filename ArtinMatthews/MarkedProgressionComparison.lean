module

public import ArtinMatthews.MarkedProgressionPositive


set_option backward.privateInPublic true
@[expose] public section

/-! A finite comparison step for replacing a nonnegative residual by its
Bonferroni truncation and explicitly averaging the positive omitted tail. -/

namespace ArtinMatthews

open scoped BigOperators

/-- Comparison of an actual weighted sum with a truncated weighted sum and
its model. All approximation terms remain explicit. -/
theorem marked_sum_comparison {ι : Type*} (U : Finset ι) (w H A T : ι → ℝ)
    (hw : ∀ u ∈ U, 0 ≤ w u) (happrox : ∀ u ∈ U, |H u - A u| ≤ T u)
    {M MA MT c : ℝ} (hmodel : |M - MA| ≤ MT) :
    |(∑ u ∈ U, w u * H u) - c * M| ≤
      |(∑ u ∈ U, w u * A u) - c * MA| +
        (∑ u ∈ U, w u * T u) + |c| * MT := by
  have hsum : |(∑ u ∈ U, w u * H u) - ∑ u ∈ U, w u * A u| ≤
      ∑ u ∈ U, w u * T u := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ u ∈ U, |w u * H u - w u * A u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        rw [← mul_sub, abs_mul, abs_of_nonneg (hw u hu)]
        exact mul_le_mul_of_nonneg_left (happrox u hu) (hw u hu)
  have hmod : |c * MA - c * M| ≤ |c| * MT := by
    rw [← mul_sub, abs_mul, abs_sub_comm MA M]
    exact mul_le_mul_of_nonneg_left hmodel (abs_nonneg c)
  have htri1 := abs_sub_le (∑ u ∈ U, w u * H u) (∑ u ∈ U, w u * A u) (c * M)
  have htri2 := abs_sub_le (∑ u ∈ U, w u * A u) (c * MA) (c * M)
  linarith

end ArtinMatthews
