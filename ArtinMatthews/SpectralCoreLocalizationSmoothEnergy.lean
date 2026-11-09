module

public import ArtinMatthews.SpectralCoreLocalizationRellich
public import ArtinMatthews.SpectralCoreLocalizationChartCompact


set_option backward.privateInPublic true
@[expose] public section

/-! Smoothness alone discharges the compact-chart integrability in the
actual localization and local Rellich interfaces. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory Set
open scoped ContDiff

theorem spectralSection_continuous (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) : Continuous F := by
  simpa only [Function.comp_def, UpperHalfPlane.ofComplex_apply] using
    hF.continuousOn.comp_continuous UpperHalfPlane.continuous_coe (fun z => z.im_pos)

theorem spectralCoreChartEnergy_integrable_of_smooth (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (A a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun z : UpperHalfPlane => ‖F z‖^2+h2SectionEnergy F z)
      {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b} :=
  (((spectralSection_continuous F hF).norm.pow 2).add
    (h2SectionEnergy_continuous F hF)).continuousOn.integrableOn_compact
      (spectralCoreChart_compact A a b ha)

theorem spectralCoreLocalization_energy_bound_smooth (φ : SchwartzMap (ℝ × ℝ) ℂ)
    {A a b : ℝ} (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : UpperHalfPlane → ℂ)
      (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
        {w : ℂ | 0 < w.im}),
      let G := spectralCoreLocalization φ ha hφ F hF
      (∫ p, ‖G p‖^2)+(∫ p, h2DirichletDensity G G p) ≤
        C*(∫ z : UpperHalfPlane in {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b},
          ‖F z‖^2+h2SectionEnergy F z) := by
  obtain ⟨C,hC,hbound⟩ := spectralCoreLocalization_energy_bound φ ha hφ
  exact ⟨C,hC,fun F hF => hbound F hF
    (spectralCoreChartEnergy_integrable_of_smooth F hF A a b ha)⟩

theorem spectralCoreLocalization_rellich_hyperbolic_smooth {J : Type*}
    (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b) (F : J → UpperHalfPlane → ℂ)
    (hF : ∀ j, ContDiffOn ℝ ∞ (fun w : ℂ => F j (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, (∫ z : UpperHalfPlane in {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b},
      ‖F j z‖^2+h2SectionEnergy (F j) z) ≤ B) :
    IsCompact (closure (range (fun j => spectralHyperbolicRectangleLp ha hab
      (spectralCoreLocalization φ ha hφ (F j) (hF j))
      (spectralCoreLocalization_support φ ha hφ (F j) (hF j))))) :=
  spectralCoreLocalization_rellich_hyperbolic φ ha hab hφ F hF
    (fun j => spectralCoreChartEnergy_integrable_of_smooth (F j) (hF j) A a b ha) hB henergy

end
end ArtinMatthews
