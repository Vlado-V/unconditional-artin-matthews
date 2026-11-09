module

public import ArtinMatthews.SpectralPolynomialMass
import Mathlib.Analysis.Normed.Module.FiniteDimension


set_option backward.privateInPublic true
@[expose] public section

/-! Finite spectral cutoff estimates give an actual summable infinite majorant. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped BigOperators
noncomputable section

theorem spectralQuadraticMass_quartic_summable
    {ι : Type*} (τ D : ι → ℝ) (hτ₁ : ∀ i, 1 ≤ τ i) (hD : ∀ i, 0 ≤ D i)
    (C : ℝ) (hC : 0 ≤ C)
    (hcut : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset ι,
      (∀ i ∈ u, τ i ≤ R) → (∑ i ∈ u, D i) ≤ C * R ^ 2) :
    Summable (fun i => D i / τ i ^ 4) := by
  classical
  letI : MeasurableSpace ι := ⊤
  letI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hIntegral (R : ℝ) (hR : 1 ≤ R) :
      IntegrableOn D {i | τ i ≤ R} (Measure.count : Measure ι) ∧
        (∫ i in {i | τ i ≤ R}, D i ∂(Measure.count : Measure ι)) ≤ C * R ^ 2 := by
    let S := {i | τ i ≤ R}
    have hS : MeasurableSet S := trivial
    have hnonneg (i : ι) : 0 ≤ S.indicator D i := by
      by_cases hi : i ∈ S <;> simp [hi, hD i]
    have hbound (u : Finset ι) : (∑ i ∈ u, S.indicator D i) ≤ C * R ^ 2 := by
      have he : (∑ i ∈ u, S.indicator D i) =
          ∑ i ∈ u.filter (fun i => τ i ≤ R), D i := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : τ i ≤ R <;> simp [S, hi]
      rw [he]
      exact hcut R hR _ (fun i hi => (Finset.mem_filter.mp hi).2)
    have hsum : Summable (S.indicator D) := summable_of_sum_le hnonneg hbound
    have hint : Integrable (S.indicator D) (Measure.count : Measure ι) :=
      integrable_count_iff.mpr hsum.norm
    refine ⟨(integrable_indicator_iff hS).mp hint, ?_⟩
    have he : (∫ i in S, D i ∂(Measure.count : Measure ι)) = ∑' i, S.indicator D i := by
      rw [← integral_indicator hS, Measure.count, integral_sum_measure hint]
      simp only [integral_dirac]
    change (∫ i in S, D i ∂(Measure.count : Measure ι)) ≤ _
    rw [he]
    exact Real.tsum_le_of_sum_le hnonneg hbound
  have hI := spectralQuadraticMass_quartic_integrable (Measure.count : Measure ι)
    τ D measurable_from_top hτ₁ hD C hC hIntegral
  have hs := integrable_count_iff.mp hI
  apply hs.congr
  intro i
  exact Real.norm_of_nonneg (div_nonneg (hD i) (by positivity))

end
end ArtinMatthews
