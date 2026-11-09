module

public import ArtinMatthews.SpectralCompactChartCover
public import ArtinMatthews.SpectralGamma0CosetCharts
public import Mathlib.MeasureTheory.Group.Integral


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine compact-chart energy domination by the actual Γ₀ core norm. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

private theorem sl_modular_measurePreserving (δ : SL(2, ℤ)) :
    MeasurePreserving (fun z : UpperHalfPlane => δ • z) volume volume := by
  change MeasurePreserving (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ δ • z) _ _
  exact measurePreserving_smul _ _

private theorem sl_modular_measurableEmbedding (δ : SL(2, ℤ)) :
    MeasurableEmbedding (fun z : UpperHalfPlane => δ • z) := by
  change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ δ • z)
  exact measurableEmbedding_const_smul _

private theorem finite_cover_integral_le_sum {K : Set UpperHalfPlane}
    (hK : MeasurableSet K) (s : Finset SL(2, ℤ))
    (hs : K ⊆ ⋃ δ ∈ s, (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd)
    (f : UpperHalfPlane → ℝ) (hf : ∀ z, 0 ≤ f z) (hKi : IntegrableOn f K)
    (hi : ∀ δ ∈ s, IntegrableOn f ((fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd)) :
    (∫ z in K, f z) ≤
      ∑ δ ∈ s, ∫ z in (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd, f z := by
  classical
  let S (δ : SL(2, ℤ)) := (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd
  have hm (δ : SL(2, ℤ)) : MeasurableSet (S δ) :=
    ModularGroup.isClosed_fd.measurableSet.preimage (sl_modular_measurePreserving δ).measurable
  have hIi (δ : SL(2, ℤ)) (hδ : δ ∈ s) : Integrable ((S δ).indicator f) :=
    (integrable_indicator_iff (hm δ)).mpr (hi δ hδ)
  have hpoint (z : UpperHalfPlane) : K.indicator f z ≤ ∑ δ ∈ s, (S δ).indicator f z := by
    by_cases hz : z ∈ K
    · obtain ⟨δ, hδ, hzδ⟩ := mem_iUnion₂.mp (hs hz)
      rw [indicator_of_mem hz]
      calc
        f z = (S δ).indicator f z := (indicator_of_mem hzδ f).symm
        _ ≤ ∑ ε ∈ s, (S ε).indicator f z := Finset.single_le_sum
          (fun ε _ => indicator_nonneg (fun _ _ => hf _) _) hδ
    · rw [indicator_of_notMem hz]
      exact Finset.sum_nonneg (fun δ _ => indicator_nonneg (fun _ _ => hf _) _)
  calc
    (∫ z in K, f z) = ∫ z, K.indicator f z := (integral_indicator hK).symm
    _ ≤ ∫ z, ∑ δ ∈ s, (S δ).indicator f z :=
      integral_mono ((integrable_indicator_iff hK).mpr hKi) (integrable_finsetSum s hIi) hpoint
    _ = ∑ δ ∈ s, ∫ z in S δ, f z := by
      rw [integral_finsetSum s hIi]
      apply Finset.sum_congr rfl
      intro δ _
      exact integral_indicator (hm δ)

/-- A compact chart has a finite energy domination constant independent of the
level and of the genuine smooth seed.  All integrability premises follow from
our actual periodization and finite-energy construction. -/
theorem compact_chart_gamma0_energy_bound {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C > 0, ∀ (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds),
      (∫ z in K, ‖gamma0PoincareSeed N ψ.val z‖ ^ 2 +
        h2SectionEnergy (gamma0PoincareSeed N ψ.val) z) ≤ C * ‖gamma0EnergyTest N ψ‖ ^ 2 := by
  classical
  obtain ⟨s, hs⟩ := compact_modular_region_cover hK
  refine ⟨(s.card : ℝ) + 1, by positivity, fun N _ ψ => ?_⟩
  let f : UpperHalfPlane → ℝ := fun z => ‖gamma0PoincareSeed N ψ.val z‖ ^ 2 +
    h2SectionEnergy (gamma0PoincareSeed N ψ.val) z
  have hf : ∀ z, 0 ≤ f z := fun z => add_nonneg (sq_nonneg _) (h2SectionEnergy_nonneg _ _)
  have hc : Continuous f := ((gamma0PoincareSeed N ψ.val).continuous.norm.pow 2).add
    (h2SectionEnergy_continuous _ (gamma0SmoothSeed_representative_smooth N ψ))
  have hfd (δ : SL(2, ℤ)) : IntegrableOn (fun z : UpperHalfPlane => f (δ⁻¹ • z)) ModularGroup.fd := by
    exact ((gamma0PoincareSeed_memLp_modularRegion N ψ.val δ⁻¹).integrable_norm_pow
      (by norm_num)).add (arithmeticPoincareSeed_energy_integrable _ ψ
        (Matrix.SpecialLinearGroup.mapGL ℝ δ⁻¹))
  have hi (δ : SL(2, ℤ)) : IntegrableOn f
      ((fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd) := by
    have he := ((sl_modular_measurePreserving δ).restrict_preimage_emb
      (sl_modular_measurableEmbedding δ) ModularGroup.fd).integrable_comp_emb
      (sl_modular_measurableEmbedding δ) (g := fun z => f (δ⁻¹ • z))
    simpa only [Function.comp_def, IntegrableOn, inv_smul_smul] using he.mpr (hfd δ)
  have hchange (δ : SL(2, ℤ)) :
      (∫ z in (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd, f z) =
        ∫ z in ModularGroup.fd, f (δ⁻¹ • z) := by
    simpa only [inv_smul_smul] using (sl_modular_measurePreserving δ).setIntegral_preimage_emb
      (sl_modular_measurableEmbedding δ) (fun z => f (δ⁻¹ • z)) ModularGroup.fd
  calc
    (∫ z in K, f z) ≤ ∑ δ ∈ s, ∫ z in (fun z : UpperHalfPlane => δ • z) ⁻¹' ModularGroup.fd, f z :=
      finite_cover_integral_le_sum hK.measurableSet s hs f hf (hc.continuousOn.integrableOn_compact hK)
        (fun δ _ => hi δ)
    _ = ∑ δ ∈ s, ∫ z in ModularGroup.fd, f (δ⁻¹ • z) := by
      apply Finset.sum_congr rfl
      exact fun δ _ => hchange δ
    _ ≤ ∑ _δ ∈ s, ‖gamma0EnergyTest N ψ‖ ^ 2 := by
      apply Finset.sum_le_sum
      exact fun δ _ => gamma0Seed_chart_energy_le N ψ δ
    _ = (s.card : ℝ) * ‖gamma0EnergyTest N ψ‖ ^ 2  := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((s.card : ℝ) + 1) * ‖gamma0EnergyTest N ψ‖ ^ 2 := by nlinarith [sq_nonneg ‖gamma0EnergyTest N ψ‖]

end ArtinMatthews
