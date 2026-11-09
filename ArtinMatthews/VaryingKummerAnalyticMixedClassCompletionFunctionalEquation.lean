module

public import ArtinMatthews.VaryingKummerAnalyticMixedClassFunctionalEquation


set_option backward.privateInPublic true
@[expose] public section

/-! Functional equation of the genuine entire nonprincipal ideal-class
completion, including the removable values at zero and one. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Filter Set Topology
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedEntireIdealClassCompletion_eq_div
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    mixedEntireIdealClassCompletion K χ s = mixedIdealClassXi K χ s / (s * (s-1)) := by
  have hw := finite_group_character_sum_eq_zero χ hχ
  unfold mixedEntireIdealClassCompletion
  rw [dslope_of_ne _ hs1, slope, dslope_of_ne _ hs0,
    dslope_of_ne _ (one_ne_zero : (1 : ℂ) ≠ 0), slope, slope]
  rw [mixedIdealClassXi_zero_of_sum_eq_zero K χ hw,
    mixedIdealClassXi_one_of_sum_eq_zero K χ hw]
  simp only [vsub_eq_sub, sub_zero, smul_eq_mul]
  field_simp
  ring

/-- Equality away from the two removed factors follows from the actual
class-Xi transform and the identity (1-s)((1-s)-1)=s(s-1). -/
theorem mixedEntireIdealClassCompletion_functional_equation_of_ne
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (mixedDiscriminantScale K : ℂ)^s * mixedEntireIdealClassCompletion K χ s =
      mixedClassRootNumber K χ * (mixedDiscriminantScale K : ℂ)^(1-s) *
        mixedEntireIdealClassCompletion K (inverseClassCharacter K χ) (1-s) := by
  have h10 : (1:ℂ)-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h11 : (1:ℂ)-s ≠ 1 := by intro H; apply hs0; linear_combination -H
  rw [mixedEntireIdealClassCompletion_eq_div K χ hχ hs0 hs1,
    mixedEntireIdealClassCompletion_eq_div K _ (inverseClassCharacter_ne_one K χ hχ) h10 h11]
  rw [show ((1:ℂ)-s)*((1-s)-1) = s*(s-1) by ring]
  simpa only [mul_div_assoc] using congrArg (fun z : ℂ => z / (s*(s-1)))
    (mixedIdealClassXi_functional_equation K χ s)

/-- Entire weighted completion of a nonprincipal ideal-class series. -/
def mixedCompletedIdealClass (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℂ) : ℂ :=
  (mixedDiscriminantScale K : ℂ)^s * mixedEntireIdealClassCompletion K χ s

theorem mixedCompletedIdealClass_entire (χ : ClassGroup (𝓞 K) →* ℂ) :
    Differentiable ℂ (mixedCompletedIdealClass K χ) :=
  (differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'))).mul
      (mixedEntireIdealClassCompletion_entire K χ)

/-- The genuine functional equation holds everywhere, with the entire
completion supplying both formerly removable points. -/
theorem mixedCompletedIdealClass_functional_equation
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) (s : ℂ) :
    mixedCompletedIdealClass K χ s = mixedClassRootNumber K χ *
      mixedCompletedIdealClass K (inverseClassCharacter K χ) (1-s) := by
  have H : mixedCompletedIdealClass K χ = fun s => mixedClassRootNumber K χ *
      mixedCompletedIdealClass K (inverseClassCharacter K χ) (1-s) := by
    apply ((mixedCompletedIdealClass_entire K χ).differentiableOn.analyticOnNhd
      isOpen_univ).eq_of_eventuallyEq
      (((mixedCompletedIdealClass_entire K _).comp
        ((differentiable_const (1:ℂ)).sub differentiable_id)).const_mul _
        |>.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2:ℂ))
    have h2 : (1:ℝ) < (2:ℂ).re := by norm_num
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2] with z hz
    simpa only [mixedCompletedIdealClass, Function.comp_apply, Pi.sub_apply, id_eq, mul_assoc] using
      mixedEntireIdealClassCompletion_functional_equation_of_ne K χ hχ
      (Complex.ne_zero_of_one_lt_re hz) (by intro H; simp [H] at hz)
  exact congrFun H s

theorem mixedCompletedIdealClass_eq_dirichlet
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    mixedCompletedIdealClass K χ s = (mixedDiscriminantScale K : ℂ)^s *
      (mixedXiNormalization K : ℂ) * mixedGammaFactor K s * idealClassDirichlet K χ s := by
  rw [mixedCompletedIdealClass, mixedEntireIdealClassCompletion_eq K χ
    (finite_group_character_sum_eq_zero χ hχ) hs]
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
