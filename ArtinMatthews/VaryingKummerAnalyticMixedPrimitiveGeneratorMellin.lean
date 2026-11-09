module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaPrimalScalar
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveHeckeMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Exact generator-normalized finite class and Mellin identities. The
scalars are the actual character values on the coprime generator quotients,
so they are compatible with the common root number of the dual transform. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) (hMt : M ≠ ⊤)

include hMt

theorem partialDirichlet_eq_generator_residue
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (G : Ideal (𝓞 K)) (hG : G ≠ ⊥)
    (hGM : IsCoprime G M) (hprodG : Ideal.span {idealModuleGenerator I M hI hM} = I*G)
    (s : ℂ) :
    ψ.partialDirichlet (integralIdealFractionalUnit I hI) s =
      (ψ.idealHom (integralIdealFractionalUnit G hG):ℂ) *
        idealModuleResidueDirichlet I M hI hM ψ.residue s := by
  have h := ψ.fixedIdeal_coefficient_eq_generator hM I hI hMt G hG hGM hprodG
  unfold partialDirichlet idealModuleResidueDirichlet
  rw [← tsum_mul_left]
  apply tsum_congr
  intro J
  let a := idealModuleIntegerElement K I hI (idealElementRepresentative _ J)
  have ha : (a:𝓞 K) ≠ 0 := by
    rw [show (a:𝓞 K) = idealIntegerElement I hI (idealElementRepresentative _ J) from
      idealModuleIntegerElement_eq_integer I hI _]
    exact EvenRayCharacter.generator_integer_ne_zero I hI J
  have hprod : Ideal.span {(a:𝓞 K)} = I * EvenRayCharacter.underlyingIdeal ⟨J.val,J.property.1⟩ := by
    rw [show (a:𝓞 K) = idealIntegerElement I hI (idealElementRepresentative _ J) from
      idealModuleIntegerElement_eq_integer I hI _]
    exact EvenRayCharacter.generator_principal_product I hI J
  have H := h (EvenRayCharacter.underlyingIdeal ⟨J.val,J.property.1⟩)
    (EvenRayCharacter.underlyingIdeal_ne_bot _) a ha hprod
  have hu : integralIdealFractionalUnit (EvenRayCharacter.underlyingIdeal ⟨J.val,J.property.1⟩)
      (EvenRayCharacter.underlyingIdeal_ne_bot ⟨J.val,J.property.1⟩) = J.val :=
    EvenRayCharacter.underlyingIdeal_unit ⟨J.val,J.property.1⟩
  rw [hu] at H
  change ψ.coefficient ⟨J.val,J.property.1⟩ = (ψ.idealHom (integralIdealFractionalUnit G hG):ℂ) * idealModuleResidueCoefficient I M hI hM ψ.residue J at H
  rw [H]
  ring

variable (G : ClassGroup (𝓞 K) → Ideal (𝓞 K)) (hG : ∀ c, G c ≠ ⊥)
variable (hGM : ∀ c, IsCoprime (G c) M)
variable (hprodG : ∀ c, Ideal.span {(idealModuleGenerator (rayClassRepresentative K 1 c) M
    (rayClassRepresentative_ne_bot K 1 c) hM)} = rayClassRepresentative K 1 c * G c)
include hMt hGM hprodG

theorem dirichlet_eq_generator_class_sum {s : ℂ} (hs : 1 < s.re) :
    ψ.dirichlet s = ∑ c : ClassGroup (𝓞 K),
      (ψ.idealHom (integralIdealFractionalUnit (G c) (hG c)):ℂ) *
        idealModuleResidueDirichlet (rayClassRepresentative K 1 c) M
          (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue s := by
  rw [ψ.dirichlet_eq_partial_class_sum hs]
  apply Finset.sum_congr rfl
  intro c _
  exact ψ.partialDirichlet_eq_generator_residue hM hMt _ _ (G c) (hG c) (hGM c) (hprodG c) s

theorem completedDirichlet_eq_generator_class_mellin {s : ℂ} (hs : 1 < s.re) :
    (torsionOrder K:ℂ)*((mixedRadialJacobian K:ℂ)*mixedGammaFactor K s)*ψ.dirichlet s =
      ∑ c : ClassGroup (𝓞 K), (ψ.idealHom (integralIdealFractionalUnit (G c) (hG c)):ℂ) *
        (((FractionalIdeal.absNorm (rayClassFractionalRepresentative K 1 c).val:ℝ):ℂ)^s *
          mellin (fun t => ∫ u in mixedUnitLogDomain K,
            mixedPrimitiveTheta K (rayClassRepresentative K 1 c) M
              (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue u t - ψ.residue 0)
            ((Module.finrank ℚ K:ℂ)*s/2)) := by
  rw [ψ.dirichlet_eq_generator_class_sum hM hMt G hG hGM hprodG hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold rayClassFractionalRepresentative
  rw [mixedPrimitiveTheta_mellin_normalized K _ M _ hM ψ.residue ψ.residue_unit hs]
  ring

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
