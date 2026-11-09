module

public import ArtinMatthews.VaryingKummerAnalyticMixedRayClassMellin
public import ArtinMatthews.VaryingKummerAnalyticMixedRayClassSum


set_option backward.privateInPublic true
@[expose] public section

/-! The exact normalized Mellin sum of the conductor-dual class theta is
the completed actual ideal-ray Dirichlet series in its convergent half-plane. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)

theorem mixedConductorDual_class_mellin_sum {s : ℂ} (hs : 1 < s.re) :
    (∑ c : ClassGroup (𝓞 K),
      ((FractionalIdeal.absNorm (mixedTraceDualIdeal K
        (mixedConductorIdeal K (rayClassRepresentative K 1 c) M
          (rayClassRepresentative_ne_bot K 1 c) hM)).val:ℝ):ℂ)^s *
      mellin (fun t => ∫ u in mixedUnitLogDomain K,
        mixedRayClassTheta K ψ
          (mixedTraceDualIdeal K (mixedConductorIdeal K (rayClassRepresentative K 1 c) M
            (rayClassRepresentative_ne_bot K 1 c) hM)) u t)
        ((Module.finrank ℚ K:ℂ)*s/2)) =
      (torsionOrder K:ℂ)*((mixedRadialJacobian K:ℂ)*mixedGammaFactor K s)*ψ.dirichlet s := by
  simp_rw [mixedRayClassTheta_mellin_normalized K ψ _ hs]
  rw [← Finset.mul_sum,ψ.conductorDual_partial_class_sum hM hs]

end
end ArtinMatthews.VaryingKummerAnalytic
