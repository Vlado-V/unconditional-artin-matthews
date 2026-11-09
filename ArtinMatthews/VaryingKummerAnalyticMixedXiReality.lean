module

public import ArtinMatthews.VaryingKummerAnalyticMixedXiBoundary
public import Mathlib.Analysis.Calculus.Deriv.Star


set_option backward.privateInPublic true
@[expose] public section

/-! Conjugation symmetry of the actual arbitrary-signature completion, proved
from its real convergent ideal series and entire analytic uniqueness. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set
open scoped NumberField nonZeroDivisors Classical BigOperators ComplexConjugate
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedIdealUnitXi_conj_ofReal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {r : ℝ} (hr : 1 < r) :
    conj (mixedIdealUnitXi K I (r : ℂ)) = mixedIdealUnitXi K I (r : ℂ) := by
  rw [mixedIdealUnitXi_real_eq_partial K I r hr]
  simp only [map_mul, map_div₀, map_sub, Complex.conj_natCast, Complex.conj_ofReal, map_ofNat]

theorem mixedCompletedDedekindXi_conj_ofReal {r : ℝ} (hr : 1 < r) :
    conj (mixedCompletedDedekindXi K (r : ℂ)) = mixedCompletedDedekindXi K (r : ℂ) := by
  have hp (a : ℝ) (ha : 0 < a) : conj ((a : ℂ)^(r : ℂ)) = (a : ℂ)^(r : ℂ) := by
    rw [← Complex.ofReal_cpow ha.le]
    exact Complex.conj_ofReal _
  unfold mixedCompletedDedekindXi
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, map_sum,
    hp _ (mixedDiscriminantScale_pos K),
    hp _ (fractionalIdeal_absNorm_pos _), mixedIdealUnitXi_conj_ofReal K _ hr]

/-- The actual Dedekind completion is of real type. -/
theorem mixedCompletedDedekindXi_conj (s : ℂ) :
    mixedCompletedDedekindXi K (conj s) = conj (mixedCompletedDedekindXi K s) := by
  let f := mixedCompletedDedekindXi K
  have hf : Differentiable ℂ f := mixedCompletedDedekindXi_entire K
  have hg : Differentiable ℂ (fun z => conj (f (conj z))) := by
    intro z
    simpa only [Function.comp_def, starRingEnd_self_apply] using (hf (conj z)).conj_conj
  have he := halfPlane_eq_of_real_eq hf.differentiableOn hg.differentiableOn
    (fun r hr => by
      rw [Complex.conj_ofReal]
      exact (mixedCompletedDedekindXi_conj_ofReal K hr).symm)
  have hall := (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := (2 : ℂ)) (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)] with z hz
      exact he hz)
  have H := congrFun hall (conj s)
  simpa only [starRingEnd_self_apply] using H

end
end ArtinMatthews.VaryingKummerAnalytic
