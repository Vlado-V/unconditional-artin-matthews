module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaDualComparison
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverse
public import ArtinMatthews.VaryingKummerAnalyticRayIdealFixedCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Actual inverse ray-character coefficients of the transformed theta.
The scalar is derived from genuine residue-coordinate and class comparisons;
there is no assumed dual packet or functional equation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

/-- The exact inverse ideal-character packet attached to the actual dual
lattice, with one norm-one scalar independent of the varying ideal and element. -/
theorem mixedPrimitiveDualRay_coefficient_exists_scalar
    (ψ : EvenIdealRayCharacter K M) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ (L : Ideal (𝓞 K)) (hL : L ≠ ⊥)
      (β : (mixedPrimitiveDualFractionalIdeal K I M).val) (_hβ : (β : K) ≠ 0)
      (_hprod : Ideal.span {(mixedPrimitiveDualIntegralEquiv K I M β : 𝓞 K)} =
        mixedPrimitiveDualIntegralIdeal K I M * L),
      (if IsCoprime L M
        then ((ψ.inverse).idealHom (integralIdealFractionalUnit L hL) : ℂ) else 0) =
        κ * ψ.residue⁻¹ (idealModuleDualResidue K I M hI hM β β.property) := by
  obtain ⟨κ₀,hκ₀,H₀⟩ := mixedPrimitiveDualWeight_exists_scalar K I M hI hM ψ.residue
  obtain ⟨κ₁,hκ₁,H₁⟩ := ψ.inverse.exists_fixedIdeal_coefficient_residue hM
    (mixedPrimitiveDualIntegralIdeal K I M) (mixedPrimitiveDualIntegralIdeal_ne_bot K I M hI hM)
  have hn : κ₀ ≠ 0 := by
    intro h
    simp [h] at hκ₀
  refine ⟨κ₁ * κ₀⁻¹,by rw [norm_mul,norm_inv,hκ₁,hκ₀,inv_one,mul_one],?_⟩
  intro L hL β hβ hprod
  have ha : (mixedPrimitiveDualIntegralEquiv K I M β : 𝓞 K) ≠ 0 := by
    intro h
    have he : mixedPrimitiveDualIntegralEquiv K I M β = 0 := Subtype.ext h
    have hz : β = 0 := (mixedPrimitiveDualIntegralEquiv K I M).injective
      (he.trans (map_zero _).symm)
    exact hβ (congrArg Subtype.val hz)
  rw [H₁ L hL (mixedPrimitiveDualIntegralEquiv K I M β) ha hprod, H₀ β]
  change κ₁ * ψ.residue⁻¹ _ = (κ₁ * κ₀⁻¹) * (κ₀ * ψ.residue⁻¹ _)
  rw [mul_assoc, ← mul_assoc κ₀⁻¹, inv_mul_cancel₀ hn, one_mul]

end
end ArtinMatthews.VaryingKummerAnalytic
