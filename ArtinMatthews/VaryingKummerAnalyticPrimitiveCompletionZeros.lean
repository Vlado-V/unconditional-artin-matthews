module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletion
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaConjugation


set_option backward.privateInPublic true
@[expose] public section

/-! Actual nonvanishing, conjugation, and critical-strip zeros of the
proper-conductor primitive completion. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Module Set
open scoped NumberField nonZeroDivisors Classical ComplexConjugate
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) (hMt : M ≠ ⊤)
variable (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue)
include hprim

theorem properCompleted_ne_zero_right {s : ℂ} (hs : 1 < s.re) :
    ψ.properCompleted hM hMt s ≠ 0 := by
  rw [ψ.properCompleted_eq_gamma_dirichlet hM hMt hprim hs]
  exact mul_ne_zero (mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
      (mixedConductorScale_pos K (integralIdealFractionalUnit M hM)).ne')))
    (mixedGammaFactor_ne_zero K (zero_lt_one.trans hs))) (ψ.dirichlet_ne_zero hs)

theorem properCompleted_ne_zero : ψ.properCompleted hM hMt ≠ 0 := by
  intro h
  exact ψ.properCompleted_ne_zero_right hM hMt hprim (s := 2) (by norm_num)
    (congrFun h 2)

theorem properCompleted_zero_strip {s : ℂ} (hs : ψ.properCompleted hM hMt s = 0) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  constructor
  · by_contra h
    have hr : 1 < (1-s).re := by simp only [Complex.sub_re,Complex.one_re]; linarith
    obtain ⟨W,hW,HW⟩ := ψ.properCompleted_functionalEquation hM hMt hprim
    have hW0 : W ≠ 0 := fun h => by simp [h] at hW
    exact (mul_ne_zero hW0 (ψ.inverse.properCompleted_ne_zero_right hM hMt
      (ψ.inverse_isPrimitive hM hprim) hr)) ((HW s).symm.trans hs)
  · by_contra h
    exact ψ.properCompleted_ne_zero_right hM hMt hprim (lt_of_not_ge h) hs

theorem properCompleted_inverse_conj (s : ℂ) :
    ψ.inverse.properCompleted hM hMt (conj s) = conj (ψ.properCompleted hM hMt s) := by
  have hp := ψ.properCompleted_entire hM hMt hprim
  have hi := ψ.inverse.properCompleted_entire hM hMt (ψ.inverse_isPrimitive hM hprim)
  have hc : Differentiable ℂ (fun z => conj (ψ.properCompleted hM hMt (conj z))) := by
    intro z
    simpa only [Function.comp_def,starRingEnd_self_apply] using (hp (conj z)).conj_conj
  have he : ψ.inverse.properCompleted hM hMt =
      fun z => conj (ψ.properCompleted hM hMt (conj z)) := by
    apply (hi.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      (hc.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2:ℂ))
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2:ℂ).re by norm_num)] with z hz
    rw [ψ.inverse.properCompleted_eq_gamma_dirichlet hM hMt (ψ.inverse_isPrimitive hM hprim) hz,
      ψ.properCompleted_eq_gamma_dirichlet hM hMt hprim (by simpa using hz)]
    rw [map_mul,map_mul]
    rw [← mixedGammaFactor_conj,← positiveReal_cpow_conj
      (mixedConductorScale_pos K (integralIdealFractionalUnit M hM))]
    simpa only [starRingEnd_self_apply] using
      congrArg (fun v : ℂ =>
        (mixedConductorScale K (integralIdealFractionalUnit M hM):ℂ)^z * mixedGammaFactor K z * v)
        (ψ.inverse_dirichlet_conj (conj z))
  simpa only [starRingEnd_self_apply] using congrFun he (conj s)

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
