module

public import ArtinMatthews.SpectralKLPhysicalTestDensity
public import ArtinMatthews.SpectralKLExponentialQuotient
public import ArtinMatthews.SpectralKLExponentialPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! Actual physical range density from compact positive tests and proved
Weierstrass approximation, with q(x)^2 as the integrable error weight. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralKLAnchorLp : Lp ℂ 2 spectralKLPhysicalMeasure :=
  spectralKLExponentialAnchor_memLp.toLp (fun x : ℝ => (spectralKLExponentialAnchor x : ℂ))

theorem spectralKLAnchorLp_norm_sq :
    ‖spectralKLAnchorLp‖^2 = ∫ x : ℝ, (spectralKLExponentialAnchor x)^2 ∂spectralKLPhysicalMeasure := by
  unfold spectralKLAnchorLp
  rw [spectral_toLp_norm_sq]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem spectralKLExponentialPolynomial_approximation_bound (f : ℝ → ℂ)
    (hf : MemLp f 2 spectralKLPhysicalMeasure) (P : Polynomial ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, ‖P.eval (t : ℂ)-spectralKLExponentialQuotient f t‖ ≤ δ) :
    ‖spectralKLExponentialPolynomialToLp P-hf.toLp f‖ ≤ δ*‖spectralKLAnchorLp‖ := by
  have hpoint (x : ℝ) (hx : 0 < x) :
      ‖spectralKLExponentialPolynomial P x-f x‖ ≤ δ*spectralKLExponentialAnchor x := by
    have hr : Real.exp (-x) ∈ Icc (0 : ℝ) 1 :=
      ⟨(Real.exp_pos _).le,(Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)).le⟩
    rw [← spectralKLExponentialQuotient_recover f hx]
    rw [show spectralKLExponentialPolynomial P x-
        (spectralKLExponentialAnchor x : ℂ)*spectralKLExponentialQuotient f (Real.exp (-x)) =
      (spectralKLExponentialAnchor x : ℂ)*(P.eval (Real.exp (-x) : ℂ)-
        spectralKLExponentialQuotient f (Real.exp (-x))) by unfold spectralKLExponentialPolynomial; ring]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (spectralKLExponentialAnchor_pos hx).le]
    exact (mul_le_mul_of_nonneg_left (hP _ hr) (spectralKLExponentialAnchor_pos hx).le).trans_eq (mul_comm _ _)
  have hsq : ‖spectralKLExponentialPolynomialToLp P-hf.toLp f‖^2 ≤ δ^2*‖spectralKLAnchorLp‖^2 := by
    unfold spectralKLExponentialPolynomialToLp
    rw [← MemLp.toLp_sub,spectral_toLp_norm_sq,spectralKLAnchorLp_norm_sq]
    have hi := (memLp_two_iff_integrable_sq_norm
      ((spectralKLExponentialPolynomial_memLp P).sub hf).aestronglyMeasurable).mp
      ((spectralKLExponentialPolynomial_memLp P).sub hf)
    calc
      _ ≤ ∫ x : ℝ, δ^2*(spectralKLExponentialAnchor x)^2 ∂spectralKLPhysicalMeasure := by
        apply integral_mono_ae hi (spectralKLExponentialAnchor_square_integrable.const_mul (δ^2))
        filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
        dsimp only [Pi.sub_apply]
        calc
          _ ≤ (δ*spectralKLExponentialAnchor x)^2 :=
            (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (spectralKLExponentialAnchor_pos hx).le)).mpr (hpoint x hx)
          _ = _ := by ring
      _ = _ := integral_const_mul _ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mp
  simpa only [mul_pow] using hsq

theorem spectralKLCompletedSynthesis_denseRange : DenseRange spectralKLCompletedSynthesis := by
  have hs : {u : Lp ℂ 2 spectralKLPhysicalMeasure | ∃ f : ℝ → ℂ,
      u =ᵐ[spectralKLPhysicalMeasure] f ∧ HasCompactSupport f ∧ Continuous f ∧ tsupport f ⊆ Ioi (0 : ℝ)} ⊆
      closure (Set.range spectralKLCompletedSynthesis) := by
    intro u hu
    obtain ⟨f,huf,hfc,hcont,hfp⟩ := hu
    have hfm : MemLp f 2 spectralKLPhysicalMeasure := (memLp_congr_ae huf).mp (Lp.memLp u)
    have hflp : hfm.toLp f = u := by
      apply Lp.ext
      exact hfm.coeFn_toLp.trans huf.symm
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let δ : ℝ := ε/(‖spectralKLAnchorLp‖+1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hden : ‖spectralKLAnchorLp‖+1 ≠ 0 := ne_of_gt (by positivity)
    have hδeq : δ*(‖spectralKLAnchorLp‖+1) = ε := by dsimp [δ]; field_simp
    obtain ⟨P,hP⟩ := spectral_complex_polynomial_approximation (spectralKLExponentialQuotient f)
      (spectralKLExponentialQuotient_continuous f hcont hfc hfp).continuousOn δ hδ
    refine ⟨spectralKLExponentialPolynomialToLp P,spectralKLExponentialPolynomialToLp_mem_range P,?_⟩
    have hn := spectralKLExponentialPolynomial_approximation_bound f hfm P δ hδ.le (fun t ht => (hP t ht).le)
    have hclose : ‖spectralKLExponentialPolynomialToLp P-u‖ < ε := by
      rw [hflp] at hn
      have hscale : δ*‖spectralKLAnchorLp‖ < ε := by nlinarith
      exact hn.trans_lt hscale
    rw [dist_comm,dist_eq_norm]
    exact hclose
  intro u
  exact (closure_minimal hs isClosed_closure) (spectralKLPhysicalMeasure_dense_compact_positive u)

theorem spectralKLCompletedSynthesis_surjective : Function.Surjective spectralKLCompletedSynthesis := by
  have hc : IsClosed (Set.range spectralKLCompletedSynthesis) :=
    spectralKLCompletedSynthesis.isometry.isClosedEmbedding.isClosed_range
  intro u
  have hu := spectralKLCompletedSynthesis_denseRange u
  rwa [hc.closure_eq] at hu

end ArtinMatthews
