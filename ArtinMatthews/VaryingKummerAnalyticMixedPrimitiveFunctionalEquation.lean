module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveNormalizedReflection
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveGeneratorContinuation
public import ArtinMatthews.VaryingKummerAnalyticMixedRayClassMellinSum
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverseNonprincipal


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine proper-conductor completed Hecke functional equation.
The all-complex theta reflection is identified with the inverse Dirichlet
series in the left half-plane and then extended by entire uniqueness. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (G : ClassGroup (𝓞 K) → Ideal (𝓞 K)) (hG : ∀ c, G c ≠ ⊥)

def generatorCompletedHecke (s : ℂ) : ℂ :=
  (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s *
    ψ.generatorCompletedMellin hM G hG s

theorem generatorCompletedHecke_entire (hres : ψ.residue ≠ 1) :
    Differentiable ℂ (ψ.generatorCompletedHecke hM G hG) :=
  (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr
    (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne'))).mul
    (ψ.generatorCompletedMellin_entire hM G hG hres)

variable (hMt : M ≠ ⊤) (hGM : ∀ c, IsCoprime (G c) M)
variable (hprodG : ∀ c, Ideal.span {(idealModuleGenerator (rayClassRepresentative K 1 c) M
    (rayClassRepresentative_ne_bot K 1 c) hM)} = rayClassRepresentative K 1 c * G c)
include hMt hGM hprodG

theorem generatorCompletedHecke_functionalEquation (hres : ψ.residue ≠ 1)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ ∀ s : ℂ,
      ψ.generatorCompletedHecke hM G hG s =
        W * ψ.inverse.generatorCompletedHecke hM G hG (1-s) := by
  let : NeZero M := ⟨hM⟩
  obtain ⟨W,hW,HW⟩ := mixedPrimitiveRayTheta_normalized_mellin_reflection K M hM ψ hMt hprim
  refine ⟨W,hW,?_⟩
  have hleft : ∀ s : ℂ, s.re < 0 →
      ψ.generatorCompletedHecke hM G hG s =
        W * ψ.inverse.generatorCompletedHecke hM G hG (1-s) := by
    intro s hs
    have hs' : 1 < (1-s).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
    have Hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun c _ => HW (rayClassRepresentative K 1 c)
        (rayClassRepresentative_ne_bot K 1 c) (G c) (hG c) (hGM c) (hprodG c) s)
    have Hdual := mixedConductorDual_class_mellin_sum K ψ.inverse hM hs'
    have Hinv := ψ.inverse.generatorCompletedMellin_eq_gamma_dirichlet hM G hG hMt hGM hprodG
      (ψ.inverse_residue_ne_one hres) hs'
    unfold generatorCompletedHecke
    rw [Hinv]
    unfold generatorCompletedMellin
    have hc := mixedResidueIdealMellinFactor_ne_zero K
    calc
      _ = (mixedResidueIdealMellinFactor K)⁻¹ *
          ∑ c : ClassGroup (𝓞 K),
            (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^s *
              (ψ.idealHom (integralIdealFractionalUnit (G c) (hG c)):ℂ) *
              (((FractionalIdeal.absNorm (rayClassFractionalRepresentative K 1 c).val:ℝ):ℂ)^s *
                mellin (fun t => ∫ u in mixedUnitLogDomain K,
                  mixedPrimitiveTheta K (rayClassRepresentative K 1 c) M
                    (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue u t)
                  ((Module.finrank ℚ K:ℂ)*s/2)) := by
        simp only [mul_assoc,← Finset.mul_sum]
        ring
      _ = _ := by
        simp only [rayClassFractionalRepresentative]
        rw [Hsum,← Finset.mul_sum,Hdual]
        unfold mixedResidueIdealMellinFactor at hc ⊢
        have ht := (mul_ne_zero_iff.mp hc).1
        have hj := (mul_ne_zero_iff.mp hc).2
        field_simp
  have he : ψ.generatorCompletedHecke hM G hG =
      fun s => W * ψ.inverse.generatorCompletedHecke hM G hG (1-s) := by
    apply ((ψ.generatorCompletedHecke_entire hM G hG hres).differentiableOn.analyticOnNhd
      isOpen_univ).eq_of_eventuallyEq
      (((ψ.inverse.generatorCompletedHecke_entire hM G hG
        (ψ.inverse_residue_ne_one hres)).comp (by fun_prop : Differentiable ℂ (fun s : ℂ => 1-s))).const_mul W
        |>.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (-1:ℂ))
    have hm : (-1:ℂ).re < (0:ℝ) := by norm_num
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hm] with s hs
    exact hleft s hs
  intro s
  exact congrFun he s

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
