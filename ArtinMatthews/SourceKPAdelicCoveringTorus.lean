module

public import ArtinMatthews.SourceKPAdelicRationalCubeCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! The full actual adelic covering torus and its rational-cube subgroup. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicCoveringTorus : Subgroup (SourceKPAdelicProjective K hζ) :=
  (sourceKPProjectiveDiagonalHom 𝔸[K]).range.comap (sourceKPAdelicProjectiveProjection K hζ)

theorem sourceKPAdelicCoveringTorus_center_mem (z : rootsOfUnity 3 K) :
    sourceKPAdelicProjectiveCenter K hζ z ∈ sourceKPAdelicCoveringTorus K hζ := by
  refine ⟨1, ?_⟩
  rw [map_one, sourceKPAdelicProjectiveCenter_projection_one]

theorem sourceKPAdelicCoveringTorus_diagonal_mem (a : IdeleGroup (𝓞 K) K) :
    sourceKPAdelicProjectiveDiagonalLift K hζ a ∈ sourceKPAdelicCoveringTorus K hζ :=
  ⟨a, (sourceKPAdelicProjectiveDiagonalLift_projection K hζ a).symm⟩

theorem sourceKPAdelicCoveringTorus_mem_iff (g : SourceKPAdelicProjective K hζ) :
    g ∈ sourceKPAdelicCoveringTorus K hζ ↔
      ∃ (z : rootsOfUnity 3 K) (a : IdeleGroup (𝓞 K) K),
        g = sourceKPAdelicProjectiveCenter K hζ z * sourceKPAdelicProjectiveDiagonalLift K hζ a := by
  constructor
  · rintro ⟨a, ha⟩
    have hk : g * (sourceKPAdelicProjectiveDiagonalLift K hζ a)⁻¹ ∈
        (sourceKPAdelicProjectiveProjection K hζ).ker := by
      change sourceKPAdelicProjectiveProjection K hζ
        (g * (sourceKPAdelicProjectiveDiagonalLift K hζ a)⁻¹) = 1
      rw [map_mul, map_inv, sourceKPAdelicProjectiveDiagonalLift_projection, ha, mul_inv_cancel]
    rw [← sourceKPAdelicProjective_exact K hζ] at hk
    obtain ⟨z, hz⟩ := hk
    refine ⟨z, a, ?_⟩
    rw [hz, inv_mul_cancel_right]
  · rintro ⟨z, a, rfl⟩
    exact (sourceKPAdelicCoveringTorus K hζ).mul_mem
      (sourceKPAdelicCoveringTorus_center_mem K hζ z)
      (sourceKPAdelicCoveringTorus_diagonal_mem K hζ a)

theorem sourceKPAdelicCubeTorus_le_coveringTorus :
    sourceKPAdelicCubeTorus K hζ ≤ sourceKPAdelicCoveringTorus K hζ := by
  rintro g ⟨p, rfl⟩
  exact ⟨p.2.val, (sourceKPAdelicCubeEmbedding_projection K hζ p).symm⟩

theorem sourceKPAdelicRationalCubeTorus_le_coveringTorus :
    sourceKPAdelicRationalCubeTorus K hζ ≤ sourceKPAdelicCoveringTorus K hζ := by
  rintro g ⟨p, rfl⟩
  apply (sourceKPAdelicCoveringTorus K hζ).mul_mem
  · exact sourceKPAdelicCubeTorus_le_coveringTorus K hζ p.1.property
  · change sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K p.2) ∈ _
    rw [sourceKPAdelicProjectiveRationalLift_diagonal]
    exact sourceKPAdelicCoveringTorus_diagonal_mem K hζ _

end
end ArtinMatthews
