module

public import ArtinMatthews.ArtinPrimitiveBoundary
public import ArtinMatthews.ArtinRayKummerSmallModulus


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive nonvanishing at one for the genuinely constructed Frobenius
ray family at the explicit discriminant-times-relative-degree-square modulus. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField RayClass
open OAI.SevenEighths.FiniteFourier
open scoped NumberField IsMulCommutative Classical
noncomputable section
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyComplex K]
local instance primitiveBoundaryModulusNeZero : NeZero (discriminantDegreeModulus K L) :=
  ⟨(discriminantDegreeModulus_pos K L).ne'⟩

/-- Actual primitive descendants retain the Frobenius ideal values away
from the explicit modulus, with their original conductor norm bound. Both
the descendant and its inverse are nonzero at one. -/
theorem discriminantDegree_exists_primitive_boundary_nonzero
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L) ≤ f)
      (Ψ : EvenIdealRayCharacter K f) (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧
      f.absNorm ≤ (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm ∧
      (∀ I : primeToModulusIdeals (rationalIdealRayModulus K (discriminantDegreeModulus K L)),
        Ψ.idealHom (I:FractionalIdealGroup K) =
          GaloisIdealCharacter.idealHom K L χ (I:FractionalIdealGroup K)) ∧
      Ψ.primitiveContinued hf hprim 1 ≠ 0 ∧
      Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 := by
  simpa only [discriminantDegreeRayCharacter_idealHom] using
    AbelianLocal.artinRay_exists_primitive_boundary_nonzero K L
      (fun χ => discriminantDegreeRayCharacter (K := K) (L := L) χ)
      (fun _ => rfl) (discr_dvd_discriminantDegreeModulus K L)
      (fun χ hχ => discriminantDegreeRayCharacter_isNonprincipal χ hχ) χ hχ

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
