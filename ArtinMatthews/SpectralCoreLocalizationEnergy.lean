module

public import ArtinMatthews.SpectralCoreLocalizationDensity


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Euclidean H1 localization from the hyperbolic mass and
Dirichlet energy of the original smooth section on its compact chart. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

theorem spectralPlaneH1Energy_eq_integralDensity (G : SchwartzMap (ℝ × ℝ) ℂ)
    (hc : HasCompactSupport (G : ℝ × ℝ → ℂ)) :
    spectralPlaneH1Energy G = ∫ p, spectralPlaneH1Density G p := by
  have hm := spectral_plane_normsq_integrable G.continuous hc
  have hd : Integrable (fun p => ‖spectralPlanePartialX G p‖^2+‖spectralPlanePartialY G p‖^2) := by
    convert (spectralPlaneH1Density_integrable G hc).sub hm using 1
    funext p
    dsimp only [spectralPlaneH1Density, Pi.sub_apply]
    ring
  exact (integral_add hm hd).symm

theorem spectralCoreLocalization_energy_bound (φ : SchwartzMap (ℝ × ℝ) ℂ)
    {A a b : ℝ} (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : UpperHalfPlane → ℂ)
      (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
        {w : ℂ | 0 < w.im}),
      IntegrableOn (fun z : UpperHalfPlane => ‖F z‖^2+h2SectionEnergy F z)
        {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b} →
      let G := spectralCoreLocalization φ ha hφ F hF
      (∫ p, ‖G p‖^2)+(∫ p, h2DirichletDensity G G p) ≤
        C*(∫ z : UpperHalfPlane in {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b},
          ‖F z‖^2+h2SectionEnergy F z) := by
  obtain ⟨M,hM,hbound⟩ := spectral_cutoff_coordinate_bound φ
  let C : ℝ := 5*M^2*(b^2+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun F hF hi => ?_⟩
  let G := spectralCoreLocalization φ ha hφ F hF
  have hG : tsupport G ⊆ spectralPlaneRectangle A a b :=
    spectralCoreLocalization_support φ ha hφ F hF
  have hc : HasCompactSupport (G : ℝ × ℝ → ℂ) :=
    (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _) hG
  have hR : MeasurableSet (spectralPlaneRectangle A a b) :=
    (spectralPlaneRectangle_compact A a b).isClosed.measurableSet
  have hpos : spectralPlaneRectangle A a b ⊆ {p : ℝ × ℝ | 0 < p.2} :=
    fun p hp => ha.trans_le hp.2.1
  have hiw := (spectralCoreChartEnergy_integrable F hR hpos).mp hi
  have hd := spectralPlaneH1Density_integrable G hc
  have hmono : (∫ p in spectralPlaneRectangle A a b, spectralPlaneH1Density G p) ≤
      ∫ p in spectralPlaneRectangle A a b, C*(spectralCoreChartEnergy F p/p.2^2) := by
    apply integral_mono_ae hd.integrableOn (hiw.const_mul C)
    filter_upwards [ae_restrict_mem hR] with p hp
    exact spectralCoreLocalizationFun_chart_bound φ F hF hM.le hbound
      (ha.trans_le hp.2.1) hp.2.2
  change (∫ p, ‖G p‖^2)+(∫ p, h2DirichletDensity G G p) ≤ _
  rw [← spectralPlaneH1Energy_eq_dirichlet G, spectralPlaneH1Energy_eq_integralDensity G hc]
  calc
    _ = ∫ p in spectralPlaneRectangle A a b, spectralPlaneH1Density G p := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      exact fun p hp => spectralPlaneH1Density_eq_zero hG hp
    _ ≤ _ := hmono
    _ = _ := by
      rw [integral_const_mul, ← spectralCoreChartEnergy_integral F hR hpos]

end
end ArtinMatthews
