module

public import ArtinMatthews.EisensteinAngularEmbedding
public import ArtinMatthews.EisensteinAngularField
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! An actual complex embedding extending the oriented Eisenstein
embedding used by the source's angular residue character. This fixes
the complex convention of the Kummer correction without a compatibility
assumption. -/

namespace ArtinMatthews.AngularLambda

open NumberField
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical

noncomputable section

variable {F : Type} [Field F] [NumberField F] {ζ : F}

def sourceComplexEmbedding (hζ : IsPrimitiveRoot ζ 12) : F →+* ℂ := by
  letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
  letI : Algebra BaseField ℂ := baseComplexEmbedding.toAlgebra
  exact (IsAlgClosed.lift (R := BaseField) (S := F) (M := ℂ)).toRingHom

theorem sourceComplexEmbedding_base (hζ : IsPrimitiveRoot ζ 12) (b : BaseField) :
    letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
    sourceComplexEmbedding hζ (algebraMap BaseField F b) = baseComplexEmbedding b := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  let : Algebra BaseField ℂ := baseComplexEmbedding.toAlgebra
  exact (IsAlgClosed.lift (R := BaseField) (S := F) (M := ℂ)).commutes b

@[instance_reducible]
def sourceComplexAlgebra (hζ : IsPrimitiveRoot ζ 12) : Algebra F ℂ :=
  (sourceComplexEmbedding hζ).toAlgebra

theorem sourceComplexAlgebra_apply (hζ : IsPrimitiveRoot ζ 12) (x : F) :
    letI : Algebra F ℂ := sourceComplexAlgebra hζ
    algebraMap F ℂ x = sourceComplexEmbedding hζ x := rfl

end

end ArtinMatthews.AngularLambda
