module

public import ArtinMatthews.VaryingKummerAnalyticMixedMellinFubini
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAnalytic
public import ArtinMatthews.VaryingKummerAnalyticDedekindSeriesPartialComplex


set_option backward.privateInPublic true
@[expose] public section

/-! The actual entire mixed-signature ideal xi is identified with the genuine
Gamma-completed partial Dedekind series throughout Re(s)>1. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField MeasureTheory Set
open NumberField.Units
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

def mixedPartialThetaCompletion (s : ℂ) : ℂ :=
  ((Module.finrank ℚ K : ℂ)*s/2) *
    ((Module.finrank ℚ K : ℂ)*s/2 - (Module.finrank ℚ K : ℂ)/2) *
    ((torsionOrder K : ℂ) * (mixedRadialJacobian K : ℂ) * mixedGammaFactor K s *
      ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^(-s) * mixedPartialDedekindDirichlet K I s)

theorem mixedPartialThetaCompletion_differentiableOn :
    DifferentiableOn ℂ (mixedPartialThetaCompletion K I) {s : ℂ | 1 < s.re} := by
  intro s hs
  have hg := mixedGammaFactor_differentiableAt K (lt_trans zero_lt_one hs)
  have hd := (mixedPartialDedekindDirichlet_analyticOnNhd K I s hs).differentiableAt
  have hp : DifferentiableAt ℂ
      (fun z : ℂ => ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ)^(-z)) s :=
    differentiableAt_id.neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (fractionalIdeal_absNorm_pos I).ne'))
  apply DifferentiableAt.differentiableWithinAt
  unfold mixedPartialThetaCompletion
  fun_prop

theorem mixedIdealUnitXi_real_eq_completion (r : ℝ) (hr : 1 < r) :
    mixedIdealUnitXi K I (r : ℂ) = mixedPartialThetaCompletion K I (r : ℂ) := by
  rw [mixedIdealUnitXi_real_eq_partial K I r hr]
  unfold mixedPartialThetaCompletion
  rw [mixedPartialDedekindDirichlet_ofReal_toReal K I hr,
    ← mixedRealGammaFactor_ofReal K r]
  simp only [mixedRealHeckeFactor, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_cpow (fractionalIdeal_absNorm_pos I).le, Complex.ofReal_neg]
  ring

/-- Genuine continuation identity, with no presumed zeta or Mellin relation. -/
theorem mixedIdealUnitXi_eq_partialCompletion {s : ℂ} (hs : 1 < s.re) :
    mixedIdealUnitXi K I s = mixedPartialThetaCompletion K I s := by
  exact halfPlane_eq_of_real_eq (mixedIdealUnitXi_entire K I).differentiableOn
    (mixedPartialThetaCompletion_differentiableOn K I)
    (mixedIdealUnitXi_real_eq_completion K I) hs

end
end ArtinMatthews.VaryingKummerAnalytic
