module

public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedSeries
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuationBase


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine arbitrary-signature ideal-class continuation and cancellation of
the two elementary completion factors for nonprincipal class characters. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField FractionalIdeal MeasureTheory Set
open scoped NumberField nonZeroDivisors Classical BigOperators Topology
variable (K : Type*) [Field K] [NumberField K]

def mixedUnitXiBoundaryConstant : ℂ :=
  ((volume.real (mixedUnitLogDomain K) * (Module.finrank ℚ K : ℝ) / 2 : ℝ) : ℂ)

theorem mixedNormalizedIdealXi_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedNormalizedIdealXi K I 0 = mixedUnitXiBoundaryConstant K := by
  simp only [mixedNormalizedIdealXi, Complex.cpow_zero, one_mul,
    mixedIdealUnitXi_zero, mixedUnitXiBoundaryConstant]

theorem mixedNormalizedIdealXi_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedNormalizedIdealXi K I 1 =
      (mixedDiscriminantScale K : ℂ)⁻¹ * mixedUnitXiBoundaryConstant K := by
  have H := mixedIdealUnitXi_weighted_reflection K I (1 : ℂ)
  simp only [Complex.cpow_one, sub_self, Complex.cpow_zero, one_mul,
    mixedIdealUnitXi_zero] at H
  have hD : (mixedDiscriminantScale K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'
  apply mul_left_cancel₀ hD
  calc
    (mixedDiscriminantScale K : ℂ) * mixedNormalizedIdealXi K I 1 =
        mixedUnitXiBoundaryConstant K := by
      simpa only [mixedNormalizedIdealXi, Complex.cpow_one, mul_assoc,
        mixedUnitXiBoundaryConstant] using H
    _ = _ := by field_simp

def mixedIdealClassXi (w : ClassGroup (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑ c : ClassGroup (𝓞 K), w c⁻¹ * mixedNormalizedIdealXi K (classRepresentative K c) s

theorem mixedIdealClassXi_entire (w : ClassGroup (𝓞 K) → ℂ) :
    Differentiable ℂ (mixedIdealClassXi K w) := by
  apply Differentiable.fun_sum
  intro c _
  exact (mixedNormalizedIdealXi_entire K _).const_mul _

theorem mixedIdealClassXi_eq (w : ClassGroup (𝓞 K) → ℂ) {s : ℂ} (hs : 1 < s.re) :
    mixedIdealClassXi K w s = (mixedXiNormalization K : ℂ) * s * (s-1) *
      mixedGammaFactor K s * idealClassDirichlet K w s := by
  unfold mixedIdealClassXi mixedNormalizedIdealXi
  simp_rw [mixedIdealUnitXi_normalized K hs]
  rw [idealClassDirichlet_partition w hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold mixedPartialDedekindDirichlet
  ring

theorem mixedIdealClassXi_zero_of_sum_eq_zero (w : ClassGroup (𝓞 K) → ℂ)
    (hw : ∑ c, w c = 0) : mixedIdealClassXi K w 0 = 0 := by
  simp only [mixedIdealClassXi, mixedNormalizedIdealXi_zero]
  have hw' : (∑ c : ClassGroup (𝓞 K), w c⁻¹) = 0 := by
    simpa only [Equiv.inv_apply, hw] using (Equiv.sum_comp (Equiv.inv (ClassGroup (𝓞 K)))) w
  rw [← Finset.sum_mul, hw', zero_mul]

theorem mixedIdealClassXi_one_of_sum_eq_zero (w : ClassGroup (𝓞 K) → ℂ)
    (hw : ∑ c, w c = 0) : mixedIdealClassXi K w 1 = 0 := by
  simp only [mixedIdealClassXi, mixedNormalizedIdealXi_one]
  have hw' : (∑ c : ClassGroup (𝓞 K), w c⁻¹) = 0 := by
    simpa only [Equiv.inv_apply, hw] using (Equiv.sum_comp (Equiv.inv (ClassGroup (𝓞 K)))) w
  rw [← Finset.sum_mul, hw', zero_mul]

theorem rayClass_entire_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ (dslope f a) := by
  rw [← differentiableOn_univ] at hf ⊢
  exact (Complex.differentiableOn_dslope (by simp : (Set.univ : Set ℂ) ∈ nhds a)).mpr hf

def mixedEntireIdealClassCompletion (w : ClassGroup (𝓞 K) → ℂ) : ℂ → ℂ :=
  dslope (dslope (mixedIdealClassXi K w) 0) 1

theorem mixedEntireIdealClassCompletion_entire (w : ClassGroup (𝓞 K) → ℂ) :
    Differentiable ℂ (mixedEntireIdealClassCompletion K w) :=
  rayClass_entire_dslope (rayClass_entire_dslope (mixedIdealClassXi_entire K w) 0) 1

theorem mixedEntireIdealClassCompletion_eq (w : ClassGroup (𝓞 K) → ℂ)
    (hw : ∑ c, w c = 0) {s : ℂ} (hs : 1 < s.re) :
    mixedEntireIdealClassCompletion K w s =
      (mixedXiNormalization K : ℂ) * mixedGammaFactor K s * idealClassDirichlet K w s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by intro H; simp [H] at hs
  unfold mixedEntireIdealClassCompletion
  rw [dslope_of_ne _ hs1, slope, dslope_of_ne _ hs0,
    dslope_of_ne _ (one_ne_zero : (1 : ℂ) ≠ 0), slope, slope]
  rw [mixedIdealClassXi_zero_of_sum_eq_zero K w hw,
    mixedIdealClassXi_one_of_sum_eq_zero K w hw, mixedIdealClassXi_eq K w hs]
  simp only [vsub_eq_sub, sub_zero, smul_eq_mul]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

theorem finite_group_character_sum_eq_zero {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) (hχ : χ ≠ 1) : ∑ g, χ g = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g, χ g ≠ 1 := by
    by_contra H
    push Not at H
    apply hχ
    ext g
    exact H g
  apply eq_zero_of_mul_eq_self_left hg
  simpa only [Finset.mul_sum, ← map_mul, Equiv.coe_mulLeft] using
    (Equiv.sum_comp (Equiv.mulLeft g) (fun g => χ g))

/-- Actual entire continuation of a nonprincipal ideal-class Dirichlet series.
The definition is entire for every class character; equality uses the proved
nonprincipal character sum, which cancels the two completion factors. -/
def mixedIdealClassContinued (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℂ) : ℂ :=
  (mixedXiNormalization K : ℂ)⁻¹ * mixedInverseGammaFactor K s *
    mixedEntireIdealClassCompletion K χ s

theorem mixedIdealClassContinued_entire (χ : ClassGroup (𝓞 K) →* ℂ) :
    Differentiable ℂ (mixedIdealClassContinued K χ) :=
  ((mixedInverseGammaFactor_entire K).const_mul _).mul
    (mixedEntireIdealClassCompletion_entire K χ)

theorem mixedIdealClassContinued_eq (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mixedIdealClassContinued K χ s = idealClassDirichlet K χ s := by
  unfold mixedIdealClassContinued
  rw [mixedEntireIdealClassCompletion_eq K χ (finite_group_character_sum_eq_zero χ hχ) hs]
  unfold mixedInverseGammaFactor
  have hC : (mixedXiNormalization K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedXiNormalization_pos K).ne'
  have hG := mixedGammaFactor_ne_zero K (by linarith : 0 < s.re)
  field_simp

end
end ArtinMatthews.VaryingKummerAnalytic
