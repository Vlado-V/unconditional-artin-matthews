module

public import ArtinMatthews.SpectralCompactChartEnergy
public import ArtinMatthews.SpectralGamma0CuspGraphCore
public import ArtinMatthews.SpectralCoreLocalizationChartCompact


set_option backward.privateInPublic true
@[expose] public section

/-! Actual compact-chart control in every modular cusp coordinate. -/

namespace ArtinMatthews
noncomputable section

open Set MeasureTheory
open scoped MatrixGroups

def gamma0CuspEnergyDensity (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (z : UpperHalfPlane) : ℝ :=
  ‖gamma0CuspSection N ψ r z‖^2+h2SectionEnergy (gamma0CuspSection N ψ r) z

theorem gamma0CuspEnergyDensity_nonneg (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (z : UpperHalfPlane) : 0 ≤ gamma0CuspEnergyDensity N ψ r z :=
  add_nonneg (sq_nonneg _) (h2SectionEnergy_nonneg _ _)

theorem gamma0CuspEnergyDensity_continuous (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) : Continuous (gamma0CuspEnergyDensity N ψ r) := by
  have hc : Continuous (gamma0CuspSection N ψ r) := by
    change Continuous ((gamma0PoincareSeed N ψ.val) ∘
      fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹ • z)
    exact (gamma0PoincareSeed N ψ.val).continuous.comp (continuous_const_smul _)
  exact (hc.norm.pow 2).add (h2SectionEnergy_continuous _ (gamma0CuspSection_smooth N ψ r))

theorem gamma0CuspEnergyDensity_integrableOn_compact (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) {K : Set UpperHalfPlane} (hK : IsCompact K) :
    IntegrableOn (gamma0CuspEnergyDensity N ψ r) K :=
  (gamma0CuspEnergyDensity_continuous N ψ r).continuousOn.integrableOn_compact hK

/-- Modular change of coordinates transfers the actual compact-chart
energy bound, uniformly in the genuine seed and level. -/
theorem compact_chart_gamma0_cusp_energy_bound (r : SL(2, ℤ)) {K : Set UpperHalfPlane}
    (hK : IsCompact K) :
    ∃ C > 0, ∀ (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds),
      (∫ z in K, gamma0CuspEnergyDensity N ψ r z) ≤ C*‖gamma0EnergyTest N ψ‖^2 := by
  let K' : Set UpperHalfPlane := (fun z : UpperHalfPlane => r • z) ⁻¹' K
  have hK' : IsCompact K' := by
    change IsCompact ((Homeomorph.smul (Matrix.SpecialLinearGroup.mapGL ℝ r) :
      UpperHalfPlane ≃ₜ UpperHalfPlane) ⁻¹' K)
    exact (Homeomorph.smul (Matrix.SpecialLinearGroup.mapGL ℝ r) :
      UpperHalfPlane ≃ₜ UpperHalfPlane).isCompact_preimage.mpr hK
  obtain ⟨C,hC,hbound⟩ := compact_chart_gamma0_energy_bound hK'
  refine ⟨C,hC,fun N _ ψ => ?_⟩
  have hmp : MeasurePreserving (fun z : UpperHalfPlane => r • z) volume volume := by
    change MeasurePreserving (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r • z) _ _
    exact measurePreserving_smul _ _
  have hme : MeasurableEmbedding (fun z : UpperHalfPlane => r • z) := by
    change MeasurableEmbedding (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ r • z)
    exact measurableEmbedding_const_smul _
  let f : UpperHalfPlane → ℝ := fun z => ‖gamma0PoincareSeed N ψ.val (r⁻¹ • z)‖^2+
    h2SectionEnergy (gamma0PoincareSeed N ψ.val) (r⁻¹ • z)
  have he : (∫ z in K', ‖gamma0PoincareSeed N ψ.val z‖^2+
      h2SectionEnergy (gamma0PoincareSeed N ψ.val) z) = ∫ z in K, f z := by
    simpa only [f,inv_smul_smul] using hmp.setIntegral_preimage_emb hme f K
  simp_rw [gamma0CuspEnergyDensity, gamma0CuspSection_energy]
  change (∫ z in K, f z) ≤ C*‖gamma0EnergyTest N ψ‖^2
  rw [← he]
  exact hbound N ψ

end
end ArtinMatthews
