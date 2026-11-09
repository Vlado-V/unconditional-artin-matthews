module

public import ArtinMatthews.SourceKPDeepMultiplier
public import ArtinMatthews.SourceKPFiniteCompactTwist


set_option backward.privateInPublic true
@[expose] public section

/-! Compatibility of the deep splitting with the exact compact
normalization used by the finite adelic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPFinitePhase_deep (g : GL (Fin 2) (P.adicCompletion K))
    (hg : SourceKPMatrixCubeData g) : sourceKPFinitePhase K hζ P g = 1 := by
  by_cases h6 : (6 : 𝓞 K) ∉ P.asIdeal
  · rw [sourceKPFinitePhase, ite_eq_left h6]
    by_cases h : g 1 0 ≠ 0 ∧ sourceKPFiniteVal K P (g 1 0) < 1 ∧ g 1 1 ≠ 0
    · rw [sourceKPCompactPhase, dite_eq_left h]
      obtain ⟨d,hd⟩ := hg.bottom_cube
      have he : Units.mk0 (g 1 1) h.2.2 = d^3 := Units.ext hd
      have hc : Units.mk0 (g 1 1) h.2.2 / GeneralLinearGroup.det g ∈
          sourceKPUnitCubes (P.adicCompletion K) := by
        rw [he]
        exact (sourceKPUnitCubes _).div_mem ⟨d,rfl⟩ hg.det_cube
      exact sourceFiniteKPHilbert_of_cube_right K hζ P (sourceKubotaX g) _ hc
    · rw [sourceKPCompactPhase, dite_eq_right h]
  · rw [sourceKPFinitePhase, ite_eq_right h6]

theorem sourceKPFiniteTwistedMultiplier_deep
    (g h : GL (Fin 2) (P.adicCompletion K))
    (hg : SourceKPMatrixCubeData g) (hh : SourceKPMatrixCubeData h)
    (hgh : SourceKPMatrixCubeData (g*h)) :
    sourceKPFiniteTwistedMultiplier K hζ P g h = 1 := by
  rw [sourceKPFiniteTwistedMultiplier, sourceKPCochainTwist,
    sourceKPFinitePhase_deep K hζ P g hg, sourceKPFinitePhase_deep K hζ P h hh,
    sourceKPFinitePhase_deep K hζ P (g*h) hgh,
    sourceFiniteKP2Multiplier_deep_cubes K hζ P g h hg hh hgh,
    one_mul, one_mul, div_one]

end
end ArtinMatthews
