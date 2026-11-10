module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Increasing Gaussian cutoffs, with a positive denominator at every index. -/
def spectralGaussianCutoff (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-t / ((n : ℝ) + 1) ^ 2)

theorem spectralGaussianCutoff_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ spectralGaussianCutoff n t := (Real.exp_pos _).le

theorem spectralGaussianCutoff_monotone {t : ℝ} (ht : 0 ≤ t) :
    Monotone (fun n => spectralGaussianCutoff n t) := by
  intro n m hnm
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div]
  apply neg_le_neg
  apply div_le_div_of_nonneg_left ht (by positivity)
  have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem spectralGaussianCutoff_tendsto (t : ℝ) :
    Tendsto (fun n => spectralGaussianCutoff n t) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := -t)).mul
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2)
  have he := Real.continuous_exp.continuousAt.tendsto.comp h
  simpa [Function.comp_def, spectralGaussianCutoff, inv_pow, div_eq_mul_inv] using he

/-- Bounded nonnegative Gaussian integrals give integrability of the full function
and convergence to its integral. No integrability of the limit is assumed. -/
theorem integrable_of_uniform_gaussian_cutoffs
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f τ : α → ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hτ_nonneg : ∀ᵐ x ∂μ, 0 ≤ τ x)
    (hweighted : ∀ n, Integrable (fun x => f x * spectralGaussianCutoff n (τ x)) μ)
    (C : ℝ) (hbound : ∀ n, ∫ x, f x * spectralGaussianCutoff n (τ x) ∂μ ≤ C) :
    Integrable f μ ∧ (∫ x, f x ∂μ ≤ C) ∧
      Tendsto (fun n => ∫ x, f x * spectralGaussianCutoff n (τ x) ∂μ)
        atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hnonneg (n : ℕ) : ∀ᵐ x ∂μ, 0 ≤ f x * spectralGaussianCutoff n (τ x) :=
    hf_nonneg.mono fun x hx => mul_nonneg hx (spectralGaussianCutoff_nonneg n (τ x))
  have hmono : ∀ᵐ x ∂μ, Monotone (fun n => f x * spectralGaussianCutoff n (τ x)) := by
    filter_upwards [hf_nonneg, hτ_nonneg] with x hx hτ
    exact (spectralGaussianCutoff_monotone hτ).const_mul hx
  have hpointwise : ∀ᵐ x ∂μ,
      Tendsto (fun n => f x * spectralGaussianCutoff n (τ x)) atTop (𝓝 (f x)) := by
    exact Filter.Eventually.of_forall fun x => by
      simpa only [mul_one] using (spectralGaussianCutoff_tendsto (τ x)).const_mul (f x)
  have hlimit := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hweighted n).aemeasurable.ennreal_ofReal)
    (hmono.mono fun x hx n m hnm => ENNReal.ofReal_le_ofReal (hx hnm))
    (hpointwise.mono fun x hx => ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx)
  have hupper (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (f x * spectralGaussianCutoff n (τ x)) ∂μ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hweighted n) (hnonneg n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hfinite : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) < ⊤ :=
    lt_of_le_of_lt (le_of_tendsto' hlimit hupper) ENNReal.ofReal_lt_top
  have hint : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf hf_nonneg).mp (ne_of_lt hfinite)
  have hreal := integral_tendsto_of_tendsto_of_monotone hweighted hint hmono hpointwise
  exact ⟨hint, le_of_tendsto' hreal hbound, hreal⟩

end
end ArtinMatthews
