module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaCommonScalar


set_option backward.privateInPublic true
@[expose] public section

/-! A single actual normalized Gauss/root factor for all transformed ideal
classes. This arithmetic identity feeds the weighted theta functional
transform; Mellin continuation is a separate theorem. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) [NeZero M]

/-- The normalized transform factor is common to every ideal class and has
modulus one. Both the Gauss factor and the ray-character comparison scalar
are derived from actual finite trace duality. -/
theorem mixedPrimitiveTheta_common_rootNumber (ψ : EvenIdealRayCharacter K M)
    (hMt : M ≠ ⊤) (hψ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
      (G : Ideal (𝓞 K)) (hG : G ≠ ⊥) (_hGM : IsCoprime G M)
      (_hprod : Ideal.span {idealModuleGenerator I M hI (NeZero.ne M)} = I*G)
      (β : (mixedPrimitiveDualFractionalIdeal K I M).val) (hβ : (β : K) ≠ 0),
      (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
        (ψ.residue⁻¹ (idealModuleDualResidue K I M hI (NeZero.ne M) β β.property) *
          idealTraceGaussSum K M ψ.residue) =
        (Real.sqrt (Ideal.absNorm M : ℝ) : ℂ) * W *
          ψ.inverse.coefficient (mixedPrimitiveDualRelativeIdeal K I M hI (NeZero.ne M) β hβ) := by
  obtain ⟨ε,hε,Hε⟩ := mixedPrimitiveTheta_common_scalar K M (NeZero.ne M) ψ hMt
  refine ⟨idealTraceRootNumber K M ψ.residue * ε,?_,?_⟩
  · rw [norm_mul,idealTraceRootNumber_norm K M ψ.residue hψ,hε,mul_one]
  · intro I hI G hG hGM hprod β hβ
    have H := Hε I hI G hG hGM hprod β hβ
    have hn : (Real.sqrt (Ideal.absNorm M : ℝ) : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      rw [← idealTraceGaussSum_norm K M ψ.residue hψ]
      exact norm_ne_zero_iff.mpr (idealTraceGaussSum_ne_zero K M ψ.residue hψ)
    calc
      _ = idealTraceGaussSum K M ψ.residue *
          ((ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
            ψ.residue⁻¹ (idealModuleDualResidue K I M hI (NeZero.ne M) β β.property)) := by ring
      _ = _ := by
        rw [H,idealTraceRootNumber]
        field_simp

end
end ArtinMatthews.VaryingKummerAnalytic
