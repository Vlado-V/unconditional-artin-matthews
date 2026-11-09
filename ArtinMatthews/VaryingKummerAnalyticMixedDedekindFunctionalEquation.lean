module

public import ArtinMatthews.VaryingKummerAnalyticMixedIdealFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedFunctionalNormalization
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualClasses


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine arbitrary-signature completed Dedekind functional equation.
Every step uses the actual trace-dual ideal and the actual ideal-class sum. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedIdealUnitXi_weighted_reflection
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (mixedDiscriminantScale K : ℂ)^s *
      ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^s * mixedIdealUnitXi K I s =
    (mixedDiscriminantScale K : ℂ)^(1-s) *
      ((FractionalIdeal.absNorm (mixedTraceDualIdeal K I).1 : ℝ) : ℂ)^(1-s) *
        mixedIdealUnitXi K (mixedTraceDualIdeal K I) (1-s) := by
  rw [mixedIdealUnitXi_functional_equation K I]
  calc
    _ = ((mixedDiscriminantScale K : ℂ)^s *
      ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^s *
      (((FractionalIdeal.absNorm I.1 : ℝ)*mixedDiscriminantScale K : ℝ) : ℂ)⁻¹ *
      (((mixedDualRadialScale K)^2 : ℝ) : ℂ)^(-((Module.finrank ℚ K : ℂ)*(1-s)/2))) *
        mixedIdealUnitXi K (mixedTraceDualIdeal K I) (1-s) := by ring
    _ = _ := by rw [mixedFunctionalEquation_coefficient K I s]

/-- The entire Dedekind completion constructed from actual mixed lattices has
the exact reflection symmetry at all complex spectral parameters. -/
theorem mixedCompletedDedekindXi_functional_equation (s : ℂ) :
    mixedCompletedDedekindXi K s = mixedCompletedDedekindXi K (1-s) := by
  unfold mixedCompletedDedekindXi
  rw [mul_assoc, mul_assoc]
  congr 1
  calc
    _ = ∑ c : ClassGroup (𝓞 K),
      (mixedDiscriminantScale K : ℂ)^s *
      ((FractionalIdeal.absNorm (classRepresentative K c).1 : ℝ) : ℂ)^s *
        mixedIdealUnitXi K (classRepresentative K c) s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = ∑ c : ClassGroup (𝓞 K),
      (mixedDiscriminantScale K : ℂ)^(1-s) *
      ((FractionalIdeal.absNorm (mixedTraceDualIdeal K (classRepresentative K c)).1 : ℝ) : ℂ)^(1-s) *
        mixedIdealUnitXi K (mixedTraceDualIdeal K (classRepresentative K c)) (1-s) := by
      apply Finset.sum_congr rfl
      intro c _
      exact mixedIdealUnitXi_weighted_reflection K (classRepresentative K c) s
    _ = (mixedDiscriminantScale K : ℂ)^(1-s) *
      ∑ c : ClassGroup (𝓞 K),
      ((FractionalIdeal.absNorm (mixedTraceDualIdeal K (classRepresentative K c)).1 : ℝ) : ℂ)^(1-s) *
        mixedIdealUnitXi K (mixedTraceDualIdeal K (classRepresentative K c)) (1-s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by rw [mixedIdealUnitXi_traceDual_normalized_class_sum K (1-s)]

end
end ArtinMatthews.VaryingKummerAnalytic
