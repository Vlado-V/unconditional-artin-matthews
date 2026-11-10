module

public import ArtinMatthews.SpectralExpPolynomialDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.SpectralExpWeightedL1
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! Approximation errors in the exact differentiable and weighted integral forms. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ContDiff Polynomial Topology
noncomputable section

theorem exists_spectralExpPolynomial_diff_envelope
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X],
      let d := fun s : ℝ => spectralExpPolynomial p s - g s
      ContDiff ℝ 2 d ∧ ∀ s : ℝ, 0 ≤ s →
        ‖d s‖ ≤ ε * Real.exp (-s) ∧
        ‖deriv d s‖ ≤ ε * Real.exp (-s) ∧
        ‖deriv (deriv d) s‖ ≤ ε * Real.exp (-s) := by
  obtain ⟨p, hp⟩ := exists_spectralExpPolynomial_C2_near g hg hc hε
  let d := fun s : ℝ => spectralExpPolynomial p s - g s
  have he := spectralExpPolynomial_contDiff p
  have he' := (contDiff_infty_iff_deriv.mp he).2
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have h₁ : deriv d = fun s => deriv (spectralExpPolynomial p) s - deriv g s := by
    funext s
    exact deriv_fun_sub ((he.differentiable (by simp)) s) ((hg.differentiable (by simp)) s)
  have h₂ (s : ℝ) : deriv (deriv d) s =
      deriv (deriv (spectralExpPolynomial p)) s - deriv (deriv g) s := by
    rw [h₁]
    exact deriv_fun_sub ((he'.differentiable (by simp)) s) ((hg'.differentiable (by simp)) s)
  have hd : ContDiff ℝ 2 d := (he.sub hg).of_le (by simp)
  refine ⟨p, hd, ?_⟩
  intro s hs
  change ‖d s‖ ≤ _ ∧ ‖deriv d s‖ ≤ _ ∧ ‖deriv (deriv d) s‖ ≤ _
  rw [h₂ s, h₁]
  exact hp s hs

theorem exists_spectralExpPolynomial_weighted_tendsto
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ p : ℕ → ℂ[X],
      let d := fun (n : ℕ) (s : ℝ) => spectralExpPolynomial (p n) s - g s
      Tendsto (fun n : ℕ => ∫ s : ℝ in Ioi 0, ‖d n s‖ / Real.sqrt s) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ∫ s : ℝ in Ioi 0, ‖d n s‖) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ∫ s : ℝ in Ioi 0,
        ‖deriv (fun t : ℝ => (t : ℂ) * deriv (d n) t) s‖) atTop (𝓝 0) := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hp (n : ℕ) := exists_spectralExpPolynomial_diff_envelope g hg hc
    (ε := ε n) (one_div_pos.mpr (by positivity))
  choose p hp using hp
  have hL (n : ℕ) := spectralExpEnvelope_weightedL1 (hp n).1 (hp n).2
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨p, ?_, ?_, ?_⟩
  · apply squeeze_zero
      (fun n => integral_nonneg fun s => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg s))
      (fun n => (hL n).1.2)
    simpa only [zero_mul] using hε.mul_const (Real.sqrt Real.pi)
  · exact squeeze_zero (fun n => integral_nonneg fun s => norm_nonneg _)
      (fun n => (hL n).2.1.2) hε
  · apply squeeze_zero (fun n => integral_nonneg fun s => norm_nonneg _)
      (fun n => (hL n).2.2.2)
    simpa only [mul_zero] using hε.const_mul (2 : ℝ)

end
end ArtinMatthews
