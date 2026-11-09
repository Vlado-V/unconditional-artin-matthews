module

public import ArtinMatthews.SpectralGaussianMonotoneLimit
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.Algebra.InfiniteSum.Real


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

/-- Uniform bounds for nonnegative Gaussian-weighted series give a bound
for the full series and convergence of its Gaussian approximations. -/
theorem spectralGaussianCutoff_tsum_monotone_limit {ι : Type*}
    (f τ : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hτ : ∀ i, 0 ≤ τ i)
    (C : ℝ)
    (hS : ∀ k : ℕ, Summable (fun i => f i * spectralGaussianCutoff k (τ i)))
    (hC : ∀ k : ℕ, (∑' i, f i * spectralGaussianCutoff k (τ i)) ≤ C) :
    Summable f ∧ (∑' i, f i) ≤ C ∧
      Tendsto (fun k : ℕ => ∑' i, f i * spectralGaussianCutoff k (τ i))
        atTop (𝓝 (∑' i, f i)) := by
  have hpoint (i : ι) :
      Tendsto (fun k : ℕ => f i * spectralGaussianCutoff k (τ i)) atTop (𝓝 (f i)) := by
    simpa only [mul_one] using (spectralGaussianCutoff_tendsto (τ i)).const_mul (f i)
  have hnonneg (k : ℕ) (i : ι) : 0 ≤ f i * spectralGaussianCutoff k (τ i) :=
    mul_nonneg (hf i) (spectralGaussianCutoff_nonneg k (τ i))
  have hfinite (U : Finset ι) : ∑ i ∈ U, f i ≤ C := by
    have hlim : Tendsto (fun k : ℕ => ∑ i ∈ U, f i * spectralGaussianCutoff k (τ i))
        atTop (𝓝 (∑ i ∈ U, f i)) :=
      tendsto_finsetSum U (fun i _ => hpoint i)
    exact le_of_tendsto' hlim (fun k =>
      ((hS k).sum_le_tsum U (fun i _ => hnonneg k i)).trans (hC k))
  have hsum : Summable f := summable_of_sum_le hf hfinite
  refine ⟨hsum, hsum.tsum_le_of_sum_le hfinite, ?_⟩
  apply tendsto_tsum_of_dominated_convergence hsum hpoint
  exact Eventually.of_forall fun k i => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg k i)]
    apply mul_le_of_le_one_right (hf i)
    calc
      spectralGaussianCutoff k (τ i) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hτ i)) (sq_nonneg _))
      _ = 1 := Real.exp_zero

end ArtinMatthews
