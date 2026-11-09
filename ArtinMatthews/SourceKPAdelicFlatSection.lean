module

public import ArtinMatthews.SourceKPAdelicFlatTorus
public import ArtinMatthews.SourceKPAdelicSectionBound


set_option backward.privateInPublic true
@[expose] public section

/-! The actual global section is flat in the spectral parameter.
Its height factor is separated from its parameter-zero coefficient. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicBorelCompact_height
    (b : sourceKPAdelicCoveringBorel K hζ) (k : sourceKPAdelicDeepCompact K hζ)
    (g : GL (Fin 2) 𝔸[K])
    (hp : sourceKPAdelicProjectiveProjection K hζ (b.val*k.val) = ProjGenLinGroup.mk g) :
    sourceKPAdelicHeight K hζ g = sourceKPIdeleAbsoluteNorm K
      (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ b)) := by
  obtain ⟨m,hm,hmp,hmd⟩ := sourceKPAdelicCoveringBorel_matrix K hζ b
  obtain ⟨k₀,hk₀⟩ := k.property
  have hg : ProjGenLinGroup.mk g = ProjGenLinGroup.mk (m*k₀.val) := by
    rw [← hp,map_mul,hmp,← hk₀,sourceKPAdelicDeepCompactLift_projection,map_mul]
  rw [sourceKPAdelicHeight_projective K hζ g (m*k₀.val) hg]
  rw [sourceKPAdelicHeight_factor K hζ (m*k₀.val) m k₀.val 1 hm k₀.property.1
    (by rw [map_one,mul_one]),hmd]

theorem sourceKPAdelicCompactScalar_flat (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) :
    sourceKPAdelicCompactScalar K hζ s q =
      Complex.exp (s * (Real.log (sourceKPAdelicHeight K hζ g) : ℂ)) *
        sourceKPAdelicCompactScalar K hζ 0 q := by
  by_cases hq : sourceCompactInducedFactorable (sourceKPAdelicCoveringBorel K hζ)
      (sourceKPAdelicDeepCompact K hζ) q
  · obtain ⟨b,k,he⟩ := hq
    have hh := sourceKPAdelicBorelCompact_height K hζ b k g (he ▸ hp)
    unfold sourceKPAdelicCompactScalar
    rw [sourceKPAdelicCompactSection_factor K hζ s q b k he,
      sourceKPAdelicCompactSection_factor K hζ 0 q b k he,
      sourceKPAdelicNormalizedBorelVector_flat,sourceKPIdeleComplexNorm_coe,hh]
  · rw [sourceKPAdelicCompactScalar_zero K hζ s q hq,
      sourceKPAdelicCompactScalar_zero K hζ 0 q hq,mul_zero]

theorem sourceKPAdelicCompactScalar_norm_flat (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hp : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) :
    ‖sourceKPAdelicCompactScalar K hζ s q‖ =
      Real.exp (s.re * Real.log (sourceKPAdelicHeight K hζ g)) *
        ‖sourceKPAdelicCompactScalar K hζ 0 q‖ := by
  rw [sourceKPAdelicCompactScalar_flat K hζ s q g hp,norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

end
end ArtinMatthews
