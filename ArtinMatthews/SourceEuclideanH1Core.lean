module

public import ArtinMatthews.SourceEuclideanH1Gradient
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts


set_option backward.privateInPublic true
@[expose] public section

/-! A compact (C^1) core has its actual distributional derivative.
Passing to the joint (L^2) limit gives the genuine Euclidean (H^1)
coordinate with its actual derivative vector. -/

namespace ArtinMatthews

open MeasureTheory TemperedDistribution Filter
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison
open scoped SchwartzMap LineDeriv ContDiff Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem sourceCompactC1_distributional_derivative (f : E → ℂ)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (m : E)
    (u v : Lp ℂ 2 (volume : Measure E)) (hu : (u : E → ℂ) =ᵐ[volume] f)
    (hv : (v : E → ℂ) =ᵐ[volume] fun x => fderiv ℝ f x m) :
    ∂_{m} (u : 𝓢'(E, ℂ)) = (v : 𝓢'(E, ℂ)) := by
  ext1 φ
  rw [TemperedDistribution.lineDerivOp_apply_apply,map_neg,Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hdf : Continuous (fun x => fderiv ℝ f x m) := hf.continuous_fderiv (by norm_num) |>.clm_apply continuous_const
  have hdφ : Continuous (fun x => fderiv ℝ (φ : E → ℂ) x m) :=
    (φ.smooth 1).continuous_fderiv (by norm_num) |>.clm_apply continuous_const
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure E))
    (f := f) (g := (φ : E → ℂ)) (v := m)
    ((hdf.mul φ.continuous).integrable_of_hasCompactSupport ((HasCompactSupport.fderiv_apply ℝ hfc m).mul_right))
    ((hf.continuous.mul hdφ).integrable_of_hasCompactSupport hfc.mul_right)
    ((hf.continuous.mul φ.continuous).integrable_of_hasCompactSupport hfc.mul_right)
    (fun x _ => (hf.differentiable (by norm_num)) x) (fun x _ => φ.differentiableAt)
  have hleft : (∫ x, (∂_{m} φ : 𝓢(E, ℂ)) x • u x) =
      ∫ x, f x * fderiv ℝ (φ : E → ℂ) x m := by
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    rw [hx,smul_eq_mul,SchwartzMap.lineDerivOp_apply_eq_fderiv,mul_comm]
  have hright : (∫ x, φ x • v x) = ∫ x, fderiv ℝ f x m * φ x := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx,smul_eq_mul,mul_comm]
  rw [hleft,hright,hparts,neg_neg]

variable {ι : Type*} [Fintype ι]

theorem sourceEuclideanH1_of_compact_core_limits (b : OrthonormalBasis ι ℝ E)
    (f : ℕ → E → ℂ) (hf : ∀ n, ContDiff ℝ 1 (f n)) (hfc : ∀ n, HasCompactSupport (f n))
    (M : Lp ℂ 2 (volume : Measure E)) (G : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (mass : ℕ → Lp ℂ 2 (volume : Measure E))
    (gradient : ℕ → Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E))
    (hm : Tendsto mass atTop (𝓝 M)) (hg : Tendsto gradient atTop (𝓝 G))
    (hma : ∀ n, (mass n : E → ℂ) =ᵐ[volume] f n)
    (hga : ∀ n i, ∀ᵐ x ∂(volume : Measure E), gradient n x i = fderiv ℝ (f n) x (b i)) :
    ∃ u : Lp ℂ 2 (volume : Measure E),
      SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u = M ∧
      (2 * Real.pi * Complex.I : ℂ) • EuclideanGradient.CM.Construction.sobolevVectorGradient b u = G := by
  apply sourceEuclideanH1_of_gradient_limits b M G mass gradient hm hg
  intro n i
  exact sourceCompactC1_distributional_derivative (f n) (hf n) (hfc n) (b i) (mass n) _
    (hma n) ((LpComponents.CM.Construction.complexLpComponent_coe (volume : Measure E) i (gradient n)).trans (hga n i))

end
end ArtinMatthews
