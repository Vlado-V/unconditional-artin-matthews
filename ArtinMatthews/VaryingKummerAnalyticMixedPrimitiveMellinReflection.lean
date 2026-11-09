module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveRayAverage
public import ArtinMatthews.VaryingKummerAnalyticMixedConductorNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! Exact all-complex Mellin reflection of the genuine averaged ray theta.
All changes of variables are unconditional Mellin identities, and the
Poisson equality is used only on its actual positive radial domain. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

theorem mellin_of_positive_reflection_dilation (f g : ℝ → ℂ) (c a s : ℂ) {b : ℝ}
    (hb : 0 < b) (hfg : ∀ t : ℝ, 0 < t → f t = c * ((t:ℂ)^(-a) * g (b*t⁻¹))) :
    mellin f s = c * (b:ℂ)^(-(a-s)) * mellin g (a-s) := by
  have he : mellin f s = mellin (fun t => c • ((t:ℂ)^(-a) • g (b*t⁻¹))) s := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [hfg t ht]
    rfl
  rw [he,mellin_const_smul,mellin_cpow_smul]
  rw [mellin_comp_inv (fun t => g (b*t)) (s + -a)]
  have hs : -(s + -a) = a-s := by ring
  rw [hs,mellin_comp_mul_left g (a-s) hb]
  simp only [smul_eq_mul,mul_assoc]

variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) [NeZero M]

theorem mixedPrimitiveRayTheta_mellin_reflection (ψ : EvenIdealRayCharacter K M)
    (hMt : M ≠ ⊤) (hψ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
      (G : Ideal (𝓞 K)) (hG : G ≠ ⊥) (_hGM : IsCoprime G M)
      (_hprod : Ideal.span {idealModuleGenerator I M hI hM} = I*G) (s : ℂ),
      (ψ.idealHom (integralIdealFractionalUnit G hG):ℂ) *
        mellin (fun t => ∫ u in mixedUnitLogDomain K,
          mixedPrimitiveTheta K I M hI hM ψ.residue u t) ((Module.finrank ℚ K:ℂ)*s/2) =
      (((FractionalIdeal.absNorm (mixedConductorIdeal K I M hI hM).val:ℝ)*
        mixedDiscriminantScale K:ℝ):ℂ)⁻¹ * (Real.sqrt (Ideal.absNorm M:ℝ):ℂ) * W *
        (((mixedDualRadialScale K)^2:ℝ):ℂ)^(-((Module.finrank ℚ K:ℂ)*(1-s)/2)) *
        mellin (fun t => ∫ u in mixedUnitLogDomain K,
          mixedRayClassTheta K ψ.inverse (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)) u t)
          ((Module.finrank ℚ K:ℂ)*(1-s)/2) := by
  obtain ⟨W,hW,HW⟩ := mixedPrimitiveRayTheta_average_poisson K M hM ψ hMt hψ
  refine ⟨W,hW,fun I hI G hG hGM hprod s => ?_⟩
  let f := fun t => ∫ u in mixedUnitLogDomain K, mixedPrimitiveTheta K I M hI hM ψ.residue u t
  let g := fun t => ∫ u in mixedUnitLogDomain K,
    mixedRayClassTheta K ψ.inverse (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)) u t
  let c : ℂ := (((FractionalIdeal.absNorm (mixedConductorIdeal K I M hI hM).val:ℝ)*
    mixedDiscriminantScale K:ℝ):ℂ)⁻¹ * (Real.sqrt (Ideal.absNorm M:ℝ):ℂ) * W
  have H := mellin_of_positive_reflection_dilation
    (fun t => (ψ.idealHom (integralIdealFractionalUnit G hG):ℂ) * f t) g c
    ((Module.finrank ℚ K:ℂ)/2) ((Module.finrank ℚ K:ℂ)*s/2)
    (sq_pos_of_pos (mixedDualRadialScale_pos K)) (fun t ht => by
      have HP := HW I hI G hG hGM hprod t ht
      dsimp only [f,g,c]
      rw [HP]
      unfold mixedPrimitivePoissonScale mixedDiscriminantScale
      simp only [Complex.ofReal_mul, Complex.ofReal_inv, mul_inv_rev,
        inv_pow, Complex.ofReal_pow]
      ring)
  have he : (Module.finrank ℚ K:ℂ)/2 - (Module.finrank ℚ K:ℂ)*s/2 =
      (Module.finrank ℚ K:ℂ)*(1-s)/2 := by ring
  rw [he] at H
  have hc : mellin (fun t => (ψ.idealHom (integralIdealFractionalUnit G hG):ℂ) * f t)
      ((Module.finrank ℚ K:ℂ)*s/2) =
      (ψ.idealHom (integralIdealFractionalUnit G hG):ℂ) * mellin f ((Module.finrank ℚ K:ℂ)*s/2) :=
    by simpa only [smul_eq_mul] using (mellin_const_smul f _ (ψ.idealHom (integralIdealFractionalUnit G hG):ℂ))
  rw [hc] at H
  exact H

end
end ArtinMatthews.VaryingKummerAnalytic
