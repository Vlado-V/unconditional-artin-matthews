module

public import ArtinMatthews.SpectralCoreLocalizationEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compactly localized hyperbolic sections satisfy the
already proved local Rellich theorem from their actual chart energy. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory Set
open scoped ContDiff

theorem spectralCoreLocalization_rellich_hyperbolic {J : Type*}
    (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b) (F : J → UpperHalfPlane → ℂ)
    (hF : ∀ j, ContDiffOn ℝ ∞ (fun w : ℂ => F j (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (hi : ∀ j, IntegrableOn (fun z : UpperHalfPlane => ‖F j z‖^2+h2SectionEnergy (F j) z)
      {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b})
    {B : ℝ} (hB : 0 ≤ B)
    (henergy : ∀ j, (∫ z : UpperHalfPlane in {z | (z.re,z.im) ∈ spectralPlaneRectangle A a b},
      ‖F j z‖^2+h2SectionEnergy (F j) z) ≤ B) :
    IsCompact (closure (range (fun j => spectralHyperbolicRectangleLp ha hab
      (spectralCoreLocalization φ ha hφ (F j) (hF j))
      (spectralCoreLocalization_support φ ha hφ (F j) (hF j))))) := by
  obtain ⟨C,hC,hbound⟩ := spectralCoreLocalization_energy_bound φ ha hφ
  apply spectral_rellich_hyperbolic_rectangle_compact_closure A a b ha hab
    (fun j => spectralCoreLocalization φ ha hφ (F j) (hF j))
    (fun j => spectralCoreLocalization_support φ ha hφ (F j) (hF j)) (mul_nonneg hC.le hB)
  intro j
  exact (hbound (F j) (hF j) (hi j)).trans (mul_le_mul_of_nonneg_left (henergy j) hC.le)

end
end ArtinMatthews
