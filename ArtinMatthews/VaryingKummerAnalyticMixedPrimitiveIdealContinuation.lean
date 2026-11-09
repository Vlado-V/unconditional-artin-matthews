module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaEntire
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaMellin
public import ArtinMatthews.VaryingKummerAnalyticMixedResidueContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine continuation of the arbitrary-ideal residue class series through
its actual mixed theta Mellin transform. No coprimality of I and M is used. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedPrimitiveIdealContinued (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (s : ℂ) : ℂ :=
  (mixedResidueIdealMellinFactor K)⁻¹ * mixedInverseGammaFactor K s *
    ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val : ℝ) : ℂ)^s *
      mellin (fun t => ∫ u in mixedUnitLogDomain K, mixedPrimitiveTheta K I M hI hM χ u t)
        ((Module.finrank ℚ K : ℂ)*s/2)

theorem mixedPrimitiveIdealContinued_entire
    (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (hχ : χ ≠ 1) :
    Differentiable ℂ (mixedPrimitiveIdealContinued K I M hI hM χ) := by
  have hm := (mixedPrimitiveTheta_unitAverage_entire K I M hI hM χ hχ).comp
    (by fun_prop : Differentiable ℂ (fun s : ℂ => (Module.finrank ℚ K : ℂ)*s/2))
  have hp := differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos (integralIdealFractionalUnit I hI)).ne'))
  exact (((mixedInverseGammaFactor_entire K).const_mul _).mul hp).mul hm

theorem mixedPrimitiveIdealContinued_eq_series
    (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ) (hχ : χ ≠ 1)
    (hunit : ∀ z : (𝓞 K)ˣ, χ (Ideal.Quotient.mk M (z:𝓞 K)) = 1)
    {s : ℂ} (hs : 1 < s.re) :
    mixedPrimitiveIdealContinued K I M hI hM χ s =
      idealModuleResidueDirichlet I M hI hM χ s := by
  let : Nontrivial ((𝓞 K) ⧸ M) := ReusedTheta.mulChar_nontrivial_domain χ hχ
  have hg := mixedGammaFactor_ne_zero K (lt_trans zero_lt_one hs)
  have hc := mixedResidueIdealMellinFactor_ne_zero K
  have hi : ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos _).ne'
  have hp : ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val : ℝ) : ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hi)
  have HM := mixedPrimitiveTheta_mellin K I M hI hM χ hunit hs
  simp only [MulChar.map_zero, sub_zero] at HM
  have HF : (torsionOrder K : ℂ)*((mixedRadialJacobian K : ℂ)*mixedGammaFactor K s) =
      mixedResidueIdealMellinFactor K * mixedGammaFactor K s := by
    unfold mixedResidueIdealMellinFactor
    ring
  rw [HF] at HM
  rw [mixedPrimitiveIdealContinued, HM, mixedInverseGammaFactor, Complex.cpow_neg]
  unfold idealModuleResidueDirichlet
  field_simp

end
end ArtinMatthews.VaryingKummerAnalytic
