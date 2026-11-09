module

public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneFunctionalEquation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual conductor-one completed equation in the positive half-plane
and the critical strip, with the shared normalization cancelled explicitly. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hMtop : M = ⊤) (hM : M ≠ ⊥)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
variable (hψ : ψ.IsNonprincipal)
include hψ hMtop

theorem conductorOneCompleted_eq_primitiveContinued_of_pos {s : ℂ} (hs : 0 < s.re) :
    ψ.conductorOneCompleted hMtop s = (mixedDiscriminantScale K : ℂ)^s *
      (mixedXiNormalization K : ℂ) * mixedGammaFactor K s *
        ψ.primitiveContinued hM hprim s := by
  have hC : (mixedXiNormalization K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos K).ne'
  have hG := mixedGammaFactor_ne_zero K hs
  rw [ψ.primitiveContinued_eq_conductorOneCompletion hMtop hM hprim hψ]
  unfold conductorOneCompleted mixedCompletedIdealClass mixedInverseGammaFactor
  field_simp

/-- Literal Gamma-times-L functional equation on the critical strip for
the primitive character whose actual conductor is the unit ideal. -/
theorem conductorOne_gamma_functional_equation {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (mixedDiscriminantScale K : ℂ)^s * mixedGammaFactor K s *
        ψ.primitiveContinued hM hprim s =
      mixedClassRootNumber K (ψ.conductorOneClassCharacter hMtop) *
        (mixedDiscriminantScale K : ℂ)^(1-s) * mixedGammaFactor K (1-s) *
          ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) (1-s) := by
  have hr : 0 < (1-s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have H := ψ.conductorOneCompleted_functional_equation hMtop hψ s
  rw [ψ.conductorOneCompleted_eq_primitiveContinued_of_pos hMtop hM hprim hψ hs0,
    ψ.inverse.conductorOneCompleted_eq_primitiveContinued_of_pos hMtop hM
      (ψ.inverse_isPrimitive hM hprim) (ψ.inverse_isNonprincipal hψ) hr] at H
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos K).ne')
  calc
    (mixedXiNormalization K : ℂ) * _ =
      (mixedDiscriminantScale K : ℂ)^s * (mixedXiNormalization K : ℂ) *
        mixedGammaFactor K s * ψ.primitiveContinued hM hprim s := by ring
    _ = _ := H
    _ = _ := by ring

/-- Reflection of genuine nontrivial zeros in the critical strip; no
functional-equation or zero-set hypothesis is supplied. -/
theorem conductorOne_primitive_zero_reflection {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ψ.primitiveContinued hM hprim s = 0 ↔
      ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) (1-s) = 0 := by
  have hr : 0 < (1-s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hD : (mixedDiscriminantScale K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'
  have hW : mixedClassRootNumber K (ψ.conductorOneClassCharacter hMtop) ≠ 0 := by
    have H := ψ.conductorOneCompleted_rootNumber_norm hMtop
    intro hz
    rw [hz,norm_zero] at H
    exact zero_ne_one H
  have H := ψ.conductorOne_gamma_functional_equation hMtop hM hprim hψ hs0 hs1
  have hz := congrArg (fun z : ℂ => z = 0) H
  apply Eq.to_iff at hz
  simpa only [mul_eq_zero, Complex.cpow_ne_zero_iff.mpr (Or.inl hD), mixedGammaFactor_ne_zero K hs0,
    mixedGammaFactor_ne_zero K hr, hW, false_or] using hz

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
