module

public import ArtinMatthews.SourceAdelicTraceHaar
public import Mathlib


set_option backward.privateInPublic true
@[expose] public section

/-! The actual full adele ring is second countable, using the frozen
finite-adele result and the real or complex archimedean completions. -/
namespace ArtinMatthews
open NumberField
open scoped NumberField AdeleRing Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

instance sourceAdelicSecondCountable_archCompletion (v : InfinitePlace F) :
    SecondCountableTopology v.Completion := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph.isEmbedding.secondCountableTopology
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph.isEmbedding.secondCountableTopology

instance sourceAdelicSecondCountable_full : SecondCountableTopology 𝔸[F] := by
  change SecondCountableTopology (InfiniteAdeleRing F × 𝔸ᶠ[F])
  have : SecondCountableTopology (InfiniteAdeleRing F) := by
    change SecondCountableTopology ((v : InfinitePlace F) → v.Completion)
    infer_instance
  infer_instance

end
end ArtinMatthews
