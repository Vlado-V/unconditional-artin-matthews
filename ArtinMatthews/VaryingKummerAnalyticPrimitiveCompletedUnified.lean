module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletionIdentity
public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneGammaEquation


set_option backward.privateInPublic true
@[expose] public section

/-! A single genuine primitive completion for every ideal conductor. The
conductor-one class completion carries an extra fixed unit-orbit normalization;
removing exactly that factor makes both branches equal to the actual conductor
power times mixed Gamma times the primitive series on the positive half-plane. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section

theorem mixedConductorScale_integral_of_top
    {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
    (hM : M ≠ ⊥) (hMtop : M = ⊤) :
    mixedConductorScale K (integralIdealFractionalUnit M hM) = mixedDiscriminantScale K := by
  subst M
  simp [mixedConductorScale]

namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)

def primitiveCompletedUnified : ℂ → ℂ :=
  if hMtop : M = ⊤ then
    fun s => (mixedXiNormalization K:ℂ)⁻¹ * ψ.conductorOneCompleted hMtop s
  else ψ.properCompleted hM hMtop

theorem primitiveCompletedUnified_of_top (hMtop : M = ⊤) :
    ψ.primitiveCompletedUnified hM =
      fun s => (mixedXiNormalization K:ℂ)⁻¹ * ψ.conductorOneCompleted hMtop s := by
  simp only [primitiveCompletedUnified,dite_eq_left hMtop]

theorem primitiveCompletedUnified_of_ne_top (hMtop : M ≠ ⊤) :
    ψ.primitiveCompletedUnified hM = ψ.properCompleted hM hMtop := by
  simp only [primitiveCompletedUnified,dite_eq_right hMtop]

theorem primitiveCompletedUnified_entire
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    Differentiable ℂ (ψ.primitiveCompletedUnified hM) := by
  by_cases hMtop : M = ⊤
  · rw [ψ.primitiveCompletedUnified_of_top hM hMtop]
    exact (ψ.conductorOneCompleted_entire hMtop).const_mul _
  · rw [ψ.primitiveCompletedUnified_of_ne_top hM hMtop]
    exact ψ.properCompleted_entire hM hMtop hprim

theorem primitiveCompletedUnified_eq_gamma_primitive
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {s : ℂ} (hs : 0 < s.re) :
    ψ.primitiveCompletedUnified hM s =
      (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s *
        mixedGammaFactor K s * ψ.primitiveContinued hM hprim s := by
  by_cases hMtop : M = ⊤
  · rw [ψ.primitiveCompletedUnified_of_top hM hMtop]
    dsimp only
    rw [ψ.conductorOneCompleted_eq_primitiveContinued_of_pos hMtop hM hprim hnp hs,
      mixedConductorScale_integral_of_top hM hMtop]
    have hC : (mixedXiNormalization K:ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos K).ne'
    calc
      _ = ((mixedXiNormalization K:ℂ)⁻¹ * (mixedXiNormalization K:ℂ)) *
          ((mixedDiscriminantScale K:ℂ)^s * mixedGammaFactor K s *
            ψ.primitiveContinued hM hprim s) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hC,one_mul]
  · rw [ψ.primitiveCompletedUnified_of_ne_top hM hMtop]
    exact ψ.properCompleted_eq_gamma_primitive_of_re_pos hM hMtop hprim hnp hs

theorem primitiveCompletedUnified_functionalEquation
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ s : ℂ,
      ψ.primitiveCompletedUnified hM s = W * ψ.inverse.primitiveCompletedUnified hM (1-s) := by
  by_cases hMtop : M = ⊤
  · refine ⟨mixedClassRootNumber K (ψ.conductorOneClassCharacter hMtop),
      ψ.conductorOneCompleted_rootNumber_norm hMtop,?_⟩
    intro s
    rw [ψ.primitiveCompletedUnified_of_top hM hMtop,
      ψ.inverse.primitiveCompletedUnified_of_top hM hMtop]
    dsimp only
    rw [ψ.conductorOneCompleted_functional_equation hMtop hnp s]
    ring
  · simpa only [ψ.primitiveCompletedUnified_of_ne_top hM hMtop,
      ψ.inverse.primitiveCompletedUnified_of_ne_top hM hMtop] using
      ψ.properCompleted_functionalEquation hM hMtop hprim

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
