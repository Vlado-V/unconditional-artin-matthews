module

public import ArtinMatthews.SourceKPLocalReceiverIntertwining
public import ArtinMatthews.SourceKPTameCompactEmbedding


set_option backward.privateInPublic true
@[expose] public section

/-! The universal receiver identifies the actual global section on
one local factor with the literal local spherical section. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀) (s : ℂ)

local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "f₀" => sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s

theorem sourceKPLocalSphericalReceiver_section (g : SourceFiniteKP2Projective K hζ P.val) :
    (sourceKPAdelicCompactSection K hζ s).val (sourceKPAdelicLocalProjective K hζ P.val g) =
      sourceKPLocalSphericalReceiver K hζ S₀ P s ((f₀).val g) := by
  obtain ⟨b, k, hg⟩ := sourceFiniteKP2Projective_Iwasawa K hζ P.val h₆ g
  rw [sourceKPAdelicCompactSection_local_factor K hζ P.val h₆ s g b k hg]
  have hf : (f₀).val g = sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀ s b
      (sourceJacquetBasis 0) := by
    rw [hg, sourceKPTameParametricSpherical_covariant K hζ S₀ P,
      sourceKPTameParametricSpherical_compact K hζ S₀ P]
  rw [hf, (sourceKPLocalSphericalReceiver K hζ S₀ P s).isIntertwining,
    sourceKPLocalSphericalReceiver_zero]

end
end ArtinMatthews
