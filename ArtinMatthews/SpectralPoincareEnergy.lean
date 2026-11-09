module

public import ArtinMatthews.SpectralGamma0Core
public import ArtinMatthews.SpectralSectionEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Compact arithmetic periodizations have actual finite Dirichlet energy. -/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped CompactlySupported MatrixGroups ContDiff

namespace ArtinMatthews

variable (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]

/-- Local finiteness closes the full union of compact support translates;
thus the actual topological support, not only the nonzero locus, is covered. -/
theorem arithmeticPoincareSeed_tsupport (ψ : C_c(UpperHalfPlane, ℂ)) :
    tsupport (arithmeticPoincareSeed 𝒢 ψ) ⊆
      ⋃ g : 𝒢, (fun z : UpperHalfPlane => g • z) ⁻¹' tsupport ψ := by
  apply closure_minimal
  · intro z hz
    obtain ⟨g, hg⟩ := arithmeticPoincareSeed_support 𝒢 ψ hz
    exact mem_iUnion.mpr ⟨g, hg⟩
  · exact (arithmetic_compact_translates_locallyFinite 𝒢 ψ.hasCompactSupport).isClosed_iUnion
      (fun g => (isClosed_tsupport ψ).preimage (continuous_const_smul g))

variable [𝒢.HasDetOne]

/-- A global bound for the actual differential energy follows from compact
support modulo the group and the proved Möbius invariance. -/
theorem arithmeticPoincareSeed_energy_bound (ψ : h2SmoothCompactSeeds) :
    ∃ C > 0, ∀ z, h2SectionEnergy (arithmeticPoincareSeed 𝒢 ψ.val) z ≤ C := by
  let F := arithmeticPoincareSeed 𝒢 ψ.val
  have hF := arithmeticPoincareSeed_smooth 𝒢 ψ.val ψ.property
  obtain ⟨C, hC⟩ := ψ.val.hasCompactSupport.exists_bound_of_continuousOn
    (h2SectionEnergy_continuous F hF).continuousOn
  refine ⟨max C 1, by positivity, fun z => ?_⟩
  by_cases hz : z ∈ tsupport F
  · obtain ⟨g, hg⟩ := mem_iUnion.mp (arithmeticPoincareSeed_tsupport 𝒢 ψ.val hz)
    have hdet : 0 < (g : GL (Fin 2) ℝ).det.val := by
      rw [Subgroup.HasDetOne.det_eq g.property]
      exact zero_lt_one
    have hinv := h2SectionEnergy_invariant F hF g hdet
      (fun z => arithmeticPoincareSeed_invariant 𝒢 ψ.val g z) z
    calc
      h2SectionEnergy F z = h2SectionEnergy F (g • z) := hinv.symm
      _ ≤ ‖h2SectionEnergy F (g • z)‖ := le_abs_self _
      _ ≤ C := hC _ hg
      _ ≤ max C 1 := le_max_left _ _
  · rw [h2SectionEnergy_eq_zero_of_notMem_tsupport F hz]
    positivity

/-- Actual energy integrability on every finite-area translated modular
region; no finite-energy hypothesis is introduced. -/
theorem arithmeticPoincareSeed_energy_integrable (ψ : h2SmoothCompactSeeds)
    (r : GL (Fin 2) ℝ) :
    IntegrableOn (fun z : UpperHalfPlane =>
      h2SectionEnergy (arithmeticPoincareSeed 𝒢 ψ.val) (r • z)) ModularGroup.fd := by
  obtain ⟨C, _, hC⟩ := arithmeticPoincareSeed_energy_bound 𝒢 ψ
  have hm : AEStronglyMeasurable (fun z : UpperHalfPlane =>
      h2SectionEnergy (arithmeticPoincareSeed 𝒢 ψ.val) (r • z))
      (volume.restrict ModularGroup.fd) := ((h2SectionEnergy_continuous _
    (arithmeticPoincareSeed_smooth 𝒢 ψ.val ψ.property)).comp
      (continuous_const_smul r)).aestronglyMeasurable
  apply (integrable_const C).mono' hm
  exact Eventually.of_forall (fun z => by
    rw [Real.norm_of_nonneg (h2SectionEnergy_nonneg _ _)]
    exact hC (r • z))

end ArtinMatthews
