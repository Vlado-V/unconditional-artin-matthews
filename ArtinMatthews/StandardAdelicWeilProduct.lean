module

public import ArtinMatthews.AdelicWeilProduct
public import ArtinMatthews.StandardAdelicWeilIndex


set_option backward.privateInPublic true
@[expose] public section

/-! Weil reciprocity for the actual standard adelic additive character.
Continuity, principal triviality, local nontriviality, and the conductor tail
are all derived for that character; no product or Fourier-family premise remains. -/

namespace ArtinMatthews.QuadraticWeil

open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem standardGaussianIndex_hasProd (b : F) (hb : b ≠ 0) :
    HasProd (fun v : ArchimedeanAdeles.Construction.Places F =>
      OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex
        (ArchimedeanAdeles.Construction.Completion F v)
        (Characters.Construction.localAdditiveCharacter F (StandardAdelic.character F) v)
        (ArchimedeanAdeles.Construction.rationalScalar F v b)) 1 :=
  adelicGaussianIndex_hasProd F (StandardAdelic.character F) (StandardAdelic.character_data F) b hb

theorem standardNormalizedWeil_hasProd (x : Fˣ) : HasProd (standardNormalizedWeil F x) 1 :=
  adelicNormalizedWeil_hasProd F (StandardAdelic.character F) (StandardAdelic.character_data F) x


end

end ArtinMatthews.QuadraticWeil
