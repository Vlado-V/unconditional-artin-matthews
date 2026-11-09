module

public import ArtinMatthews.SpectralJOddSynthesis
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open MeasureTheory Set
noncomputable section

private theorem spectralJOddGaussian_majorant (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (p : ℝ) (hp : 1 / 4 < p) :
    ∃ G : ℝ → ℝ, Integrable G ∧ ∀ k : ℕ, ∀ x : ℝ,
      ‖(Real.exp (-(p * x ^ 2)) : ℂ) * spectralJOddSynthesisTerm f k x‖ ≤
        (1 / 2 : ℝ) ^ k * G x := by
  obtain ⟨C, A, hC, hA, hcoeff⟩ := spectralJDiscreteCoefficient_factorial_bound f hf hc hs
  let b : ℝ := p - 1 / 4
  have hb : 0 < b := sub_pos.mpr hp
  let d : ℝ := A ^ 2 / (2 * b)
  let G : ℝ → ℝ := fun x => (2 * C * Real.exp d) * Real.exp (-(b / 2) * x ^ 2)
  refine ⟨G, (integrable_exp_neg_mul_sq (by positivity : 0 < b / 2)).const_mul _, ?_⟩
  intro k x
  have hx : A * |x| ≤ (b / 2) * x ^ 2 + d := by
    calc
      _ ≤ ((b * |x|) ^ 2 + A ^ 2) / (2 * b) := by
        apply (le_div_iff₀ (by positivity : 0 < 2 * b)).2
        nlinarith only [sq_nonneg (b * |x| - A)]
      _ = _ := by
        rw [mul_pow, sq_abs]
        dsimp [d]
        field_simp [hb.ne']
        <;> ring
  calc
    _ = Real.exp (-(p * x ^ 2)) * ‖spectralJOddSynthesisTerm f k x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-(p * x ^ 2)) *
        ((1 / 2 : ℝ) ^ k * (2 * C * Real.exp (x ^ 2 / 4 + A * |x|))) :=
      mul_le_mul_of_nonneg_left (spectralJOddSynthesisTerm_norm_le_geometric f hC hA hcoeff k x)
        (Real.exp_pos _).le
    _ = (1 / 2 : ℝ) ^ k * (2 * C * Real.exp (-(b * x ^ 2) + A * |x|)) := by
      rw [show -(b * x ^ 2) + A * |x| = -(p * x ^ 2) + (x ^ 2 / 4 + A * |x|) by
        dsimp [b]; ring, Real.exp_add (-(p * x ^ 2)) (x ^ 2 / 4 + A * |x|)]
      ring
    _ ≤ (1 / 2 : ℝ) ^ k * (2 * C * Real.exp (-(b / 2) * x ^ 2 + d)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (by linarith only [hx])
    _ = _ := by rw [Real.exp_add]; dsimp [G]; ring

/-- Gaussian integration of the actual odd synthesis and termwise integration of its series.
The Gaussian measure here is the weight `exp (-p * x^2)` against ordinary positive `dx`. -/
theorem spectralJOddSynthesis_gaussian (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (p : ℝ) (hp : 1 / 4 < p) :
    IntegrableOn (fun x : ℝ => (Real.exp (-(p * x ^ 2)) : ℂ) * spectralJOddSynthesis f x)
        (Ioi (0 : ℝ)) ∧
      HasSum (fun k : ℕ =>
        (2 : ℂ) * ((2 * k + 1 : ℕ) : ℂ) * spectralJDiscreteCoefficient f (2 * k + 1) *
          ∫ x in Ioi (0 : ℝ), (Real.exp (-(p * x ^ 2)) : ℂ) *
            Complex.besselJ ((2 * k + 1 : ℕ) : ℂ) (x : ℂ))
        (∫ x in Ioi (0 : ℝ), (Real.exp (-(p * x ^ 2)) : ℂ) * spectralJOddSynthesis f x) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let g : ℝ → ℂ := fun x => (Real.exp (-(p * x ^ 2)) : ℂ)
  let F : ℕ → ℝ → ℂ := fun k x => g x * spectralJOddSynthesisTerm f k x
  have hg : Continuous g := by dsimp [g]; fun_prop
  obtain ⟨G, hG, hbound⟩ := spectralJOddGaussian_majorant f hf hc hs p hp
  have hGμ : Integrable G μ := hG.integrableOn
  have hpoint (x : ℝ) : HasSum (fun k => F k x) (g x * spectralJOddSynthesis f x) :=
    (spectralJOddSynthesis_summable_norm f hf hc hs x).of_norm.hasSum.mul_left (g x)
  have hF (k : ℕ) : Integrable (F k) μ :=
    (hGμ.const_mul ((1 / 2 : ℝ) ^ k)).mono'
      (hg.mul (spectralJOddSynthesisTerm_continuous f k)).aestronglyMeasurable
      (ae_of_all _ (hbound k))
  have habs : Summable (fun k => ∫ x, ‖F k x‖ ∂μ) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (f := fun k => (1 / 2 : ℝ) ^ k * ∫ x, G x ∂μ) ?_
      (summable_geometric_two.mul_right _)
    intro k
    rw [← integral_const_mul]
    exact integral_mono_ae (hF k).norm (hGμ.const_mul _) (ae_of_all _ (hbound k))
  have htotal : Integrable (fun x => g x * spectralJOddSynthesis f x) μ :=
    (hGμ.const_mul 2).mono' (hg.mul (spectralJOddSynthesis_continuous f hf hc hs)).aestronglyMeasurable
      (ae_of_all _ fun x =>
        (hpoint x).norm_le_of_bounded (hasSum_geometric_two.mul_right (G x)) (fun k => hbound k x))
  have hsum := hasSum_integral_of_summable_integral_norm hF habs
  have hsum_integral :
      (∫ x, ∑' k, F k x ∂μ) = ∫ x, g x * spectralJOddSynthesis f x ∂μ :=
    integral_congr_ae (ae_of_all _ fun x => (hpoint x).tsum_eq)
  rw [hsum_integral] at hsum
  refine ⟨htotal, ?_⟩
  convert hsum using 1
  funext k
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [F, g, spectralJOddSynthesisTerm]
  ring

theorem spectralJOddSynthesis_gaussian_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (p : ℝ) (hp : 1 / 4 < p) :
    IntegrableOn (fun x : ℝ => (Real.exp (-(p * x ^ 2)) : ℂ) * spectralJOddSynthesis f x)
      (Ioi (0 : ℝ)) :=
  (spectralJOddSynthesis_gaussian f hf hc hs p hp).1

theorem spectralJOddSynthesis_gaussian_hasSum (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (p : ℝ) (hp : 1 / 4 < p) :
    HasSum (fun k : ℕ =>
      (2 : ℂ) * ((2 * k + 1 : ℕ) : ℂ) * spectralJDiscreteCoefficient f (2 * k + 1) *
        ∫ x in Ioi (0 : ℝ), (Real.exp (-(p * x ^ 2)) : ℂ) *
          Complex.besselJ ((2 * k + 1 : ℕ) : ℂ) (x : ℂ))
      (∫ x in Ioi (0 : ℝ), (Real.exp (-(p * x ^ 2)) : ℂ) * spectralJOddSynthesis f x) :=
  (spectralJOddSynthesis_gaussian f hf hc hs p hp).2

end
end ArtinMatthews
