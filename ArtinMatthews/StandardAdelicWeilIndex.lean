module

public import ArtinMatthews.AdelicWeilIndex
public import ArtinMatthews.StandardAdelicCharacterData


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

def standardNormalizedWeil (x : Fˣ) (v : ArchimedeanAdeles.Construction.Places F) : ℂ :=
  adelicNormalizedWeil F (StandardAdelic.character F) x v

theorem standardNormalizedWeil_square_mul (x y : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) :
    standardNormalizedWeil F (x * y ^ 2) v = standardNormalizedWeil F x v :=
  adelicNormalizedWeil_square_mul F (StandardAdelic.character F) (StandardAdelic.character_data F) x y v

theorem standardNormalizedWeil_eighth (x : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) : standardNormalizedWeil F x v ^ 8 = 1 :=
  adelicNormalizedWeil_eighth F (StandardAdelic.character F) (StandardAdelic.character_data F) x v

theorem standardNormalizedWeil_ne_zero (x : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) : standardNormalizedWeil F x v ≠ 0 :=
  adelicNormalizedWeil_ne_zero F (StandardAdelic.character F) (StandardAdelic.character_data F) x v

theorem standardNormalizedWeil_one (v : ArchimedeanAdeles.Construction.Places F) :
    standardNormalizedWeil F 1 v = 1 :=
  adelicNormalizedWeil_one F (StandardAdelic.character F) (StandardAdelic.character_data F) v

end

end ArtinMatthews.QuadraticWeil
