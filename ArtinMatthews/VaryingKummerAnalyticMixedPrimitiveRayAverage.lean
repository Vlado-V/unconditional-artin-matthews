module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveRayReflection


set_option backward.privateInPublic true
@[expose] public section

/-! The actual unit-averaged ray theta transform, with exact conductor,
discriminant, radial dilation and a single common root number. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) [NeZero M]

/-- Averaging uses the actual Dirichlet-unit fundamental domain and removes
its affine reflection by proved periodicity, not an assumed domain symmetry. -/
theorem mixedPrimitiveRayTheta_average_poisson (ψ : EvenIdealRayCharacter K M)
    (hMt : M ≠ ⊤) (hψ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
      (G : Ideal (𝓞 K)) (hG : G ≠ ⊥) (_hGM : IsCoprime G M)
      (_hprod : Ideal.span {idealModuleGenerator I M hI hM} = I*G)
      (t : ℝ) (_ht : 0 < t),
      (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
        (∫ u in mixedUnitLogDomain K, mixedPrimitiveTheta K I M hI hM ψ.residue u t) =
      mixedPrimitivePoissonScale K I M hI hM t *
        (Real.sqrt (Ideal.absNorm M : ℝ) : ℂ) * W *
          ∫ u in mixedUnitLogDomain K,
            mixedRayClassTheta K ψ.inverse (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM))
              u ((mixedDualRadialScale K)^2*t⁻¹) := by
  obtain ⟨W,hW,HW⟩ := mixedPrimitiveRayTheta_poisson K M hM ψ hMt hψ
  refine ⟨W,hW,fun I hI G hG hGM hprod t ht => ?_⟩
  rw [← integral_const_mul]
  calc
    _ = ∫ u in mixedUnitLogDomain K,
        mixedPrimitivePoissonScale K I M hI hM t *
          (Real.sqrt (Ideal.absNorm M : ℝ) : ℂ) * W *
            mixedPrimitiveRayDualTheta K I M hI hM ψ (-u) t⁻¹ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => HW I hI G hG hGM hprod u t ht)
    _ = _ := by
      rw [integral_const_mul,mixedPrimitiveRayDualTheta_average]

end
end ArtinMatthews.VaryingKummerAnalytic
