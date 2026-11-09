module

public import ArtinMatthews.SpectralNativeEigenOrder
public import ArtinMatthews.SpectralKLPowerAnalysis
public import ArtinMatthews.SpectralWeylHeightCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Literal height cutoffs pass through the actual K-order integral
throughout the closed ambient eigenvalue strip. -/

noncomputable section
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped Topology
namespace ArtinMatthews

theorem spectralKLPower_order_cutoff_tendsto (f : ℝ → ℂ) (hf : Measurable f)
    {a M B β : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (hβ : 0 ≤ β) (hβB : β < B)
    (hpower : ∀ x, 0 < x → ‖f x‖ ≤ M*x^B) (ν : ℂ) (hν : |ν.re| ≤ β) :
    Tendsto (fun K : ℕ => ∫ x in Ioi (0 : ℝ), schlafliBesselK ν x*
      (spectralWeylProfileCutoff a K f x/(x : ℂ))) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), schlafliBesselK ν x*(f x/(x : ℂ)))) := by
  have hi := spectralKLPower_analysis_integrable f hf M B β hM hβ hβB hpower ν hν
  have hik (K : ℕ) := spectralKLPower_analysis_integrable (spectralWeylProfileCutoff a K f)
    (spectralWeylProfileCutoff_measurable a K f hf) M B β hM hβ hβB
    (fun x hx => (spectralWeylProfileCutoff_norm_le a K f x).trans (hpower x hx)) ν hν
  apply tendsto_integral_of_dominated_convergence
    (fun x => ‖schlafliBesselK ν x*(f x/(x : ℂ))‖)
  · exact fun K => (hik K).aestronglyMeasurable
  · exact hi.norm
  · intro K
    filter_upwards with x
    change ‖schlafliBesselK ν x*(spectralWeylProfileCutoff a K f x/(x : ℂ))‖ ≤
      ‖schlafliBesselK ν x*(f x/(x : ℂ))‖
    have he : schlafliBesselK ν x*(spectralWeylProfileCutoff a K f x/(x : ℂ)) =
        (spectralHeightAnnularPartial K (a*x) : ℂ)*(schlafliBesselK ν x*(f x/(x : ℂ))) := by
      unfold spectralWeylProfileCutoff
      ring
    rw [he,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (spectralHeightAnnularPartial_bounds K (a*x)).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (spectralHeightAnnularPartial_bounds K (a*x)).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [spectralHeightAnnularPartial_eventually_one (mul_pos ha hx)] with K hK
    simp only [spectralWeylProfileCutoff,hK,Complex.ofReal_one,one_mul]

theorem spectralKLPower_eigen_order_integrable (f : ℝ → ℂ) (hf : Measurable f)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 1/2 < B)
    (hpower : ∀ x, 0 < x → ‖f x‖ ≤ M*x^B) (eig : ℝ) (heig : 0 ≤ eig) :
    IntegrableOn (fun x : ℝ => schlafliBesselK (Complex.sqrt (1/4-(eig : ℂ))) x*
      (f x/(x : ℂ))) (Ioi (0 : ℝ)) :=
  spectralKLPower_analysis_integrable f hf M B (1/2) hM (by norm_num) hB hpower _
    (spectralNonnegativeEnergy_order_abs_re_le eig heig)

end ArtinMatthews
