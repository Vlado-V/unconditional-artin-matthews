module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveGeneratorMellin
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! The generator-normalized theta construction gives the same genuine
primitive continuation. The proof uses the actual Dirichlet series in its
convergent half-plane and analytic uniqueness, not a scalar convention. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module MeasureTheory Set Filter
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥)
variable (G : ClassGroup (𝓞 K) → Ideal (𝓞 K)) (hG : ∀ c, G c ≠ ⊥)

def generatorContinued (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K), (ψ.idealHom (integralIdealFractionalUnit (G c) (hG c)):ℂ) *
    mixedPrimitiveIdealContinued K (rayClassRepresentative K 1 c) M
      (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue s

theorem generatorContinued_entire (hres : ψ.residue ≠ 1) :
    Differentiable ℂ (ψ.generatorContinued hM G hG) := by
  apply Differentiable.fun_sum
  intro c _
  exact (mixedPrimitiveIdealContinued_entire K _ M _ hM ψ.residue hres).const_mul _

/-- Completed theta Mellin function with the exact torsion/Jacobian factor removed. -/
def generatorCompletedMellin (s : ℂ) : ℂ :=
  (mixedResidueIdealMellinFactor K)⁻¹ *
    ∑ c : ClassGroup (𝓞 K), (ψ.idealHom (integralIdealFractionalUnit (G c) (hG c)):ℂ) *
      (((FractionalIdeal.absNorm (rayClassFractionalRepresentative K 1 c).val:ℝ):ℂ)^s *
        mellin (fun t => ∫ u in mixedUnitLogDomain K,
          mixedPrimitiveTheta K (rayClassRepresentative K 1 c) M
            (rayClassRepresentative_ne_bot K 1 c) hM ψ.residue u t)
          ((Module.finrank ℚ K:ℂ)*s/2))

theorem generatorCompletedMellin_entire (hres : ψ.residue ≠ 1) :
    Differentiable ℂ (ψ.generatorCompletedMellin hM G hG) := by
  apply Differentiable.const_mul
  apply Differentiable.fun_sum
  intro c _
  apply Differentiable.const_mul
  apply Differentiable.mul
  · exact differentiable_id.const_cpow (Or.inl
      (Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos _).ne'))
  · exact (mixedPrimitiveTheta_unitAverage_entire K _ M _ hM ψ.residue hres).comp
      (by fun_prop : Differentiable ℂ (fun s : ℂ => (Module.finrank ℚ K:ℂ)*s/2))

variable (hMt : M ≠ ⊤) (hGM : ∀ c, IsCoprime (G c) M)
variable (hprodG : ∀ c, Ideal.span {(idealModuleGenerator (rayClassRepresentative K 1 c) M
    (rayClassRepresentative_ne_bot K 1 c) hM)} = rayClassRepresentative K 1 c * G c)
include hMt hGM hprodG

theorem generatorContinued_eq_dirichlet (hres : ψ.residue ≠ 1)
    {s : ℂ} (hs : 1 < s.re) : ψ.generatorContinued hM G hG s = ψ.dirichlet s := by
  rw [ψ.dirichlet_eq_generator_class_sum hM hMt G hG hGM hprodG hs]
  unfold generatorContinued
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact mixedPrimitiveIdealContinued_eq_series K _ M _ hM ψ.residue hres ψ.residue_unit hs

theorem generatorContinued_eq_primitiveContinued (hres : ψ.residue ≠ 1)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) :
    ψ.generatorContinued hM G hG = ψ.primitiveContinued hM hprim := by
  apply ((ψ.generatorContinued_entire hM G hG hres).differentiableOn.analyticOnNhd
    isOpen_univ).eq_of_eventuallyEq
      ((ψ.primitiveContinued_entire hM hprim).differentiableOn.analyticOnNhd isOpen_univ)
      (z₀ := (2:ℂ))
  have h2 : (1:ℝ) < (2:ℂ).re := by norm_num
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2] with s hs
  rw [ψ.generatorContinued_eq_dirichlet hM G hG hMt hGM hprodG hres hs,
    ψ.primitiveContinued_eq_dirichlet hM hprim hnp hs]


theorem generatorCompletedMellin_eq_gamma_dirichlet (hres : ψ.residue ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ψ.generatorCompletedMellin hM G hG s = mixedGammaFactor K s * ψ.dirichlet s := by
  let : Nontrivial ((𝓞 K) ⧸ M) := ReusedTheta.mulChar_nontrivial_domain ψ.residue hres
  have H := ψ.completedDirichlet_eq_generator_class_mellin hM hMt G hG hGM hprodG hs
  simp only [MulChar.map_zero,sub_zero] at H
  unfold generatorCompletedMellin
  rw [← H]
  have hc := mixedResidueIdealMellinFactor_ne_zero K
  unfold mixedResidueIdealMellinFactor at hc ⊢
  field_simp
  apply (div_eq_iff hc).2
  ring

theorem generatorCompletedMellin_eq_gamma_primitive (hres : ψ.residue ≠ 1)
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal) {s : ℂ} (hs : 1 < s.re) :
    ψ.generatorCompletedMellin hM G hG s =
      mixedGammaFactor K s * ψ.primitiveContinued hM hprim s := by
  rw [ψ.generatorCompletedMellin_eq_gamma_dirichlet hM G hG hMt hGM hprodG hres hs,
    ψ.primitiveContinued_eq_dirichlet hM hprim hnp hs]

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
