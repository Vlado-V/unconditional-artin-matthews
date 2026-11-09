module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindGrowth
public import ArtinMatthews.VaryingKummerAnalyticRayUnramifiedClassXi
public import ArtinMatthews.VaryingKummerAnalyticSubquadraticSlopeGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Actual subquadratic growth for ideal-class character Xi sums and their
entire completions after cancellation of the elementary factors. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open ArtinMatthews.ReusedGrowth
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem mixedNormalizedIdealXi_hasSubquadraticGrowth
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    HasSubquadraticGrowth (mixedNormalizedIdealXi K I) :=
  (hasSubquadraticGrowth_const_cpow (fractionalIdeal_absNorm_pos I)).mul
    (mixedIdealUnitXi_hasSubquadraticGrowth K I)

theorem mixedIdealClassXi_hasSubquadraticGrowth (w : ClassGroup (𝓞 K) → ℂ) :
    HasSubquadraticGrowth (mixedIdealClassXi K w) := by
  apply HasSubquadraticGrowth.finset_sum Finset.univ
  intro c _
  exact (hasSubquadraticGrowth_const _).mul
    (mixedNormalizedIdealXi_hasSubquadraticGrowth K (classRepresentative K c))

theorem mixedEntireIdealClassCompletion_hasSubquadraticGrowth
    (w : ClassGroup (𝓞 K) → ℂ) :
    HasSubquadraticGrowth (mixedEntireIdealClassCompletion K w) := by
  have hf := mixedIdealClassXi_entire K w
  have hg := rayClass_entire_dslope hf 0
  exact ((mixedIdealClassXi_hasSubquadraticGrowth K w).dslope hf.continuous 0 (hf 0)).dslope
    hg.continuous 1 (hg 1)

theorem scaledMixedEntireIdealClassCompletion_hasSubquadraticGrowth
    (w : ClassGroup (𝓞 K) → ℂ) {A : ℝ} (hA : 0 < A) :
    HasSubquadraticGrowth (fun s => (A:ℂ)^s * mixedEntireIdealClassCompletion K w s) :=
  (hasSubquadraticGrowth_const_cpow hA).mul
    (mixedEntireIdealClassCompletion_hasSubquadraticGrowth K w)

end
end ArtinMatthews.VaryingKummerAnalytic
