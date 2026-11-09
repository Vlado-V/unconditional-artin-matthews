module

public import ArtinMatthews.ArtinPrimitiveCompletedBoundary
public import ArtinMatthews.ArtinRayKummerSmallModulus


set_option backward.privateInPublic true
@[expose] public section

/-! Endpoint nonvanishing for the actual Frobenius primitive completions
at the explicit discriminant-times-degree-square conductor bound. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField RayClass
open OAI.SevenEighths.FiniteFourier
open scoped NumberField IsMulCommutative Classical
noncomputable section
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyComplex K]
local instance completedBoundaryModulusNeZero : NeZero (discriminantDegreeModulus K L) :=
  ⟨(discriminantDegreeModulus_pos K L).ne'⟩

/-- The explicit arithmetic Frobenius family admits genuine primitive
completions nonzero at both endpoints, in both conductor branches. -/
theorem discriminantDegree_exists_primitive_completed_boundary_nonzero
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L) ≤ f)
      (Ψ : EvenIdealRayCharacter K f) (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧
      f.absNorm ≤ (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm ∧
      (∀ I : primeToModulusIdeals (rationalIdealRayModulus K (discriminantDegreeModulus K L)),
        Ψ.idealHom (I:FractionalIdealGroup K) =
          GaloisIdealCharacter.idealHom K L χ (I:FractionalIdealGroup K)) ∧
      (∀ hft : f ≠ ⊤, Ψ.properCompleted hf hft 0 ≠ 0 ∧ Ψ.properCompleted hf hft 1 ≠ 0) ∧
      (∀ hft : f = ⊤, Ψ.conductorOneCompleted hft 0 ≠ 0 ∧ Ψ.conductorOneCompleted hft 1 ≠ 0) ∧
      Ψ.primitiveContinued hf hprim 1 ≠ 0 := by
  simpa only [discriminantDegreeRayCharacter_idealHom] using
    AbelianLocal.artinRay_exists_primitive_completed_boundary_nonzero K L
      (fun χ => discriminantDegreeRayCharacter (K := K) (L := L) χ)
      (fun _ => rfl) (discr_dvd_discriminantDegreeModulus K L)
      (fun χ hχ => discriminantDegreeRayCharacter_isNonprincipal χ hχ) χ hχ

/-- Both genuine completions in the inverse pair are nonzero at zero and
one, retaining the actual Frobenius ideal values and explicit conductor bound. -/
theorem discriminantDegree_exists_primitive_completed_pair_boundary_nonzero
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
      (_hMf : rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L) ≤ f)
      (Ψ : EvenIdealRayCharacter K f) (hprim : IsPrimitiveOnIdeals Ψ.residue),
      Ψ.IsNonprincipal ∧
      f.absNorm ≤ (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L)).absNorm ∧
      (∀ I : primeToModulusIdeals (rationalIdealRayModulus K (discriminantDegreeModulus K L)),
        Ψ.idealHom (I:FractionalIdealGroup K) =
          GaloisIdealCharacter.idealHom K L χ (I:FractionalIdealGroup K)) ∧
      (∀ hft : f ≠ ⊤,
        Ψ.properCompleted hf hft 0 ≠ 0 ∧ Ψ.properCompleted hf hft 1 ≠ 0 ∧
        Ψ.inverse.properCompleted hf hft 0 ≠ 0 ∧ Ψ.inverse.properCompleted hf hft 1 ≠ 0) ∧
      (∀ hft : f = ⊤,
        Ψ.conductorOneCompleted hft 0 ≠ 0 ∧ Ψ.conductorOneCompleted hft 1 ≠ 0 ∧
        Ψ.inverse.conductorOneCompleted hft 0 ≠ 0 ∧
        Ψ.inverse.conductorOneCompleted hft 1 ≠ 0) ∧
      Ψ.primitiveContinued hf hprim 1 ≠ 0 ∧
      Ψ.inverse.primitiveContinued hf (Ψ.inverse_isPrimitive hf hprim) 1 ≠ 0 := by
  simpa only [discriminantDegreeRayCharacter_idealHom] using
    AbelianLocal.artinRay_exists_primitive_completed_pair_boundary_nonzero K L
      (fun χ => discriminantDegreeRayCharacter (K := K) (L := L) χ)
      (fun _ => rfl) (discr_dvd_discriminantDegreeModulus K L)
      (fun χ hχ => discriminantDegreeRayCharacter_isNonprincipal χ hχ) χ hχ

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
