module

public import ArtinMatthews.SourceKPResidualUnitNormalization
public import ArtinMatthews.SourceKPResidualGenericity


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCuspResidualFourierValue_unit_exists_ne_zero
    (P : HeightOneSpectrum (𝓞 K)) {T : ℝ} (hT : 1 ≤ T) :
    ∃ qf : SourceKPFiniteAdeleProjective K hζ, sourceKPCuspResidualFourierValue K hζ 1 hT qf ≠ 0 := by
  obtain ⟨m,qf,hm⟩ := sourceKPCuspResidualFourierValue_exists_ne_zero K hζ P hT
  refine ⟨sourceKPCuspResidualUnitTranslate K hζ m qf,?_⟩
  rw [sourceKPCuspResidualFourierValue_unit_translate K hζ m qf hT]
  exact mul_ne_zero (sourceKPCuspResidualFrequencyScale_ne_zero K hζ m (1/6)) hm

end
end ArtinMatthews
