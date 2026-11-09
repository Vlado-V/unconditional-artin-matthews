module

public import ArtinMatthews.ArtinPrimitiveBoundary
public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneGammaEquation


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Frobenius primitive conductor-one completions are nonzero at
zero and one. The proved Artin residue identity supplies the boundary value
at one; the genuine inverse-character functional equation supplies zero. -/
namespace ArtinMatthews.AbelianLocal
open ArtinMatthews.VaryingKummerAnalytic NumberField RayClass
open OAI.SevenEighths.FiniteFourier
open scoped NumberField IsMulCommutative Classical ComplexConjugate
noncomputable section
variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [IsAbelianGalois F E]
variable {N : ℕ} [NeZero N]
variable (ψ : (Gal(E/F) →* ℂˣ) → EvenRayCharacter F N)
variable (hψ : ∀ χ, (ψ χ).idealHom = GaloisIdealCharacter.idealHom F E χ)
variable (hD : (NumberField.discr E).natAbs ∣ N)
variable (hnp : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
variable (χ : Gal(E/F) →* ℂˣ) (hχ : χ ≠ 1)
variable (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
variable (hMf : rationalModulusIdeal (𝓞 F) N ≤ f) (Ψ : EvenIdealRayCharacter F f)
variable (hprim : IsPrimitiveOnIdeals Ψ.residue)
variable (hagree : ∀ I : primeToModulusIdeals (rationalIdealRayModulus F N),
  Ψ.idealHom (I:FractionalIdealGroup F) = (ψ χ).idealHom (I:FractionalIdealGroup F))
include hψ hD hnp hχ hMf hagree hf hprim


theorem artinRay_conductorOneCompleted_one_ne_zero (hft : f = ⊤) :
    Ψ.conductorOneCompleted hft 1 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  rw [Ψ.conductorOneCompleted_eq_primitiveContinued_of_pos hft hf hprim hΨ
    (s := 1) (by norm_num),Complex.cpow_one]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos F).ne')
    (Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos F).ne'))
    (mixedGammaFactor_ne_zero F (s := 1) (by norm_num)))
    (artinRay_primitiveContinued_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree)

theorem artinRay_inverse_conductorOneCompleted_one_ne_zero (hft : f = ⊤) :
    Ψ.inverse.conductorOneCompleted hft 1 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  rw [Ψ.inverse.conductorOneCompleted_eq_primitiveContinued_of_pos hft hf
    (Ψ.inverse_isPrimitive hf hprim) (Ψ.inverse_isNonprincipal hΨ)
    (s := 1) (by norm_num),Complex.cpow_one]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos F).ne')
    (Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos F).ne'))
    (mixedGammaFactor_ne_zero F (s := 1) (by norm_num)))
    (artinRay_inverse_primitiveContinued_one_ne_zero F E ψ hψ hD hnp χ hχ f hf hMf Ψ hprim hagree)

theorem artinRay_conductorOneCompleted_zero_ne_zero (hft : f = ⊤) :
    Ψ.conductorOneCompleted hft 0 ≠ 0 := by
  have hΨ := (ψ χ).primitiveIdeal_isNonprincipal f hMf Ψ hagree (hnp χ hχ)
  rw [Ψ.conductorOneCompleted_functional_equation hft hΨ 0,sub_zero]
  apply mul_ne_zero
  · intro hz
    have H := Ψ.conductorOneCompleted_rootNumber_norm hft
    rw [hz,norm_zero] at H
    exact zero_ne_one H
  · exact artinRay_inverse_conductorOneCompleted_one_ne_zero F E ψ hψ hD hnp χ hχ
      f hf hMf Ψ hprim hagree hft

end
end ArtinMatthews.AbelianLocal
