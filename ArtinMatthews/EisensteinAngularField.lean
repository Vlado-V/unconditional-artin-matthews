module

public import ArtinMatthews.EisensteinAngularNorm
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots


set_option backward.privateInPublic true
@[expose] public section

/-! Construct the actual Eisenstein subfield embedding from a primitive
cube root, or from the primitive twelfth root in the source's field. -/
namespace ArtinMatthews.AngularLambda
open scoped Classical
noncomputable section

local instance : IsCyclotomicExtension {3} ℚ BaseField :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

variable {F : Type*} [Field F] [CharZero F] {ζ : F}

def baseEmbeddingOfCubeRoot (hζ : IsPrimitiveRoot ζ 3) : BaseField →ₐ[ℚ] F :=
  ((IsCyclotomicExtension.zeta_spec 3 ℚ BaseField).embeddingsEquivPrimitiveRoots F
    (Polynomial.cyclotomic.irreducible_rat (by decide))).symm
      ⟨ζ,(mem_primitiveRoots (by decide)).mpr hζ⟩

theorem baseEmbeddingOfCubeRoot_zeta (hζ : IsPrimitiveRoot ζ 3) :
    baseEmbeddingOfCubeRoot hζ (IsCyclotomicExtension.zeta 3 ℚ BaseField) = ζ := by
  have h := ((IsCyclotomicExtension.zeta_spec 3 ℚ BaseField).embeddingsEquivPrimitiveRoots F
    (Polynomial.cyclotomic.irreducible_rat (by decide))).apply_symm_apply
      ⟨ζ,(mem_primitiveRoots (by decide)).mpr hζ⟩
  simpa only [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe,baseEmbeddingOfCubeRoot] using
    congrArg Subtype.val h

@[instance_reducible]
def baseAlgebraOfCubeRoot (hζ : IsPrimitiveRoot ζ 3) : Algebra BaseField F :=
  (baseEmbeddingOfCubeRoot hζ).toRingHom.toAlgebra

omit [CharZero F] in
theorem primitiveCubeRoot_of_twelve (hζ : IsPrimitiveRoot ζ 12) : IsPrimitiveRoot (ζ^4) 3 := by
  simpa using hζ.pow_of_dvd (p := 4) (by decide) (by decide)

@[instance_reducible]
def baseAlgebraOfTwelve (hζ : IsPrimitiveRoot ζ 12) : Algebra BaseField F :=
  baseAlgebraOfCubeRoot (primitiveCubeRoot_of_twelve hζ)

def cyclotomicAngularIdeal [NumberField F] (hζ : IsPrimitiveRoot ζ 12) : Ideal (NumberField.RingOfIntegers F) →*₀ ℂ := by
  letI := baseAlgebraOfTwelve hζ
  exact angularNormIdeal F

end
end ArtinMatthews.AngularLambda
