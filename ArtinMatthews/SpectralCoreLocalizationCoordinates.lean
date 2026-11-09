module

public import ArtinMatthews.SpectralCoreLocalizationDerivatives


set_option backward.privateInPublic true
@[expose] public section

/-! Actual chart-energy coordinate integrals and their integrability. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory Set

theorem upperHalfPlane_integrableOn_coordinates (G : ℝ × ℝ → ℝ)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    IntegrableOn (fun z : UpperHalfPlane => G (z.re,z.im)) {z | (z.re,z.im) ∈ S} ↔
      IntegrableOn (fun p => G p/p.2^2) S := by
  classical
  have h := upperHalfPlane_integrable_coordinates (S.indicator G)
  have hleft : (fun z : UpperHalfPlane => S.indicator G (z.re,z.im)) =
      {z : UpperHalfPlane | (z.re,z.im) ∈ S}.indicator (fun z => G (z.re,z.im)) := by
    funext z
    by_cases hz : (z.re,z.im) ∈ S <;> simp [hz]
  have hright : (fun p : ℝ × ℝ => S.indicator G p/p.2^2) =
      S.indicator (fun p => G p/p.2^2) := by
    funext p
    by_cases hp : p ∈ S <;> simp [hp]
  have hpre : MeasurableSet {z : UpperHalfPlane | (z.re,z.im) ∈ S} :=
    hS.preimage (by fun_prop)
  rw [hleft, integrable_indicator_iff hpre, hright] at h
  change IntegrableOn (fun z : UpperHalfPlane => G (z.re,z.im)) {z | (z.re,z.im) ∈ S} ↔
    Integrable (S.indicator (fun p => G p/p.2^2)) (volume.restrict {p : ℝ × ℝ | 0 < p.2}) at h
  rw [integrable_indicator_iff hS] at h
  simp only [IntegrableOn, Measure.restrict_restrict_of_subset hpositive] at h
  exact h

def spectralCoreChartEnergy (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖spectralSectionPlane F p‖^2+
    h2SectionEnergy F (UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p))

theorem spectralCoreChartEnergy_at_upper (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    spectralCoreChartEnergy F (z.re,z.im) = ‖F z‖^2+h2SectionEnergy F z := by
  have hc : Complex.equivRealProdCLM.symm (z.re,z.im) = (z : ℂ) :=
    Complex.equivRealProdCLM.symm_apply_apply (z : ℂ)
  simp only [spectralCoreChartEnergy, spectralSectionPlane, hc, UpperHalfPlane.ofComplex_apply]

theorem spectralCoreChartEnergy_nonneg (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) :
    0 ≤ spectralCoreChartEnergy F p :=
  add_nonneg (sq_nonneg _) (h2SectionEnergy_nonneg _ _)

theorem spectralCoreChartEnergy_integral (F : UpperHalfPlane → ℂ)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    (∫ z : UpperHalfPlane in {z | (z.re,z.im) ∈ S}, ‖F z‖^2+h2SectionEnergy F z) =
      ∫ p in S, spectralCoreChartEnergy F p/p.2^2 := by
  simpa only [spectralCoreChartEnergy_at_upper] using
    upperHalfPlane_setIntegral_coordinates (spectralCoreChartEnergy F) hS hpositive

theorem spectralCoreChartEnergy_integrable (F : UpperHalfPlane → ℂ)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    IntegrableOn (fun z : UpperHalfPlane => ‖F z‖^2+h2SectionEnergy F z)
      {z | (z.re,z.im) ∈ S} ↔
      IntegrableOn (fun p => spectralCoreChartEnergy F p/p.2^2) S := by
  simpa only [spectralCoreChartEnergy_at_upper] using
    upperHalfPlane_integrableOn_coordinates (spectralCoreChartEnergy F) hS hpositive

end
end ArtinMatthews
