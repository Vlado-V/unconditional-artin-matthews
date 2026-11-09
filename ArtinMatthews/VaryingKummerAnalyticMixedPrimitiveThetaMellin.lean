module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaUnfolding
public import ArtinMatthews.VaryingKummerAnalyticMixedResidueMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Mellin binding of arbitrary ideal-conductor theta to its literal
unit-invariant class Dirichlet series, with the exact χ(0) constant removed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedPrimitiveMellinKernel_eq_ideal_sum
    (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (M) (z:𝓞 K)) = 1)
    (s : ℂ) (p : ℝ × logSpace K) (ht : 0 < p.1) :
    (p.1:ℂ)^((Module.finrank ℚ K:ℂ)*s/2-1) * (mixedPrimitiveTheta K I M hI hM χ p.2 p.1 - χ 0) =
      ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
        idealModuleResidueCoefficient I M hI hM χ J *
          mixedUnitOrbitMellinKernel K (idealElementRepresentative _ J).1.1 s p := by
  rw [mixedPrimitiveTheta_ideal_units K I M hI hM χ hunit _ ht,← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [mixedUnitOrbitMellinKernel_eq_gaussian]
  ring

theorem mixedPrimitiveTheta_mellin
    (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)
    (χ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hunit : ∀ z : (𝓞 K)ˣ,
      χ (Ideal.Quotient.mk (M) (z:𝓞 K)) = 1)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => ∫ u in mixedUnitLogDomain K, (mixedPrimitiveTheta K I M hI hM χ u t - χ 0))
      ((Module.finrank ℚ K:ℂ)*s/2) =
      (torsionOrder K : ℂ) * ((mixedRadialJacobian K : ℂ) * mixedGammaFactor K s) *
        ((FractionalIdeal.absNorm (integralIdealFractionalUnit I hI).val:ℝ):ℂ)^(-s) *
          ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
            idealModuleResidueCoefficient I M hI hM χ J *
              ((FractionalIdeal.absNorm J.1.val:ℝ):ℂ)^(-s) := by
  let F := fun p : ℝ × logSpace K =>
    ∑' J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
      idealModuleResidueCoefficient I M hI hM χ J *
        mixedUnitOrbitMellinKernel K (idealElementRepresentative _ J).1.1 s p
  have HI : Integrable F ((volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K))) :=
    integrable_weightedMixedIdealUnitOrbits K _ _
      (fun J => idealModuleResidueElementWeight_norm_le_one I M hI hM χ _) hs
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ u in mixedUnitLogDomain K, F (t,u) := by
      unfold mellin
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [smul_eq_mul,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      exact mixedPrimitiveMellinKernel_eq_ideal_sum K I M hI hM χ hunit s (t,u) ht
    _ = ∫ p, F p ∂(volume.restrict (Ioi 0)).prod (volume.restrict (mixedUnitLogDomain K)) :=
      (integral_prod F HI).symm
    _ = _ := integral_weightedMixedIdealUnitOrbits K _ _
      (fun J => idealModuleResidueElementWeight_norm_le_one I M hI hM χ _) hs

end
end ArtinMatthews.VaryingKummerAnalytic
