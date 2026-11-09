module

public import ArtinMatthews.VaryingKummerAnalyticMixedDedekindCompletion
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! Logarithmic differentiation of the genuine mixed-signature completion.
The nonvanishing of the Dedekind series is supplied separately by its Euler
product theorem. -/
noncomputable section
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Set Filter
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-- Exact logarithmic derivative of the actual completion on its convergent
half-plane, with the Dedekind nonvanishing condition exposed for instantiation. -/
theorem mixedCompletedDedekindXi_logDeriv_of_zeta_ne_zero {s : ℂ}
    (hs : 1 < s.re) (hz : NumberField.dedekindZeta K s ≠ 0) :
    logDeriv (mixedCompletedDedekindXi K) s =
      1 / s + 1 / (s - 1) + (Real.log (mixedDiscriminantScale K) : ℂ) +
        logDeriv (mixedGammaFactor K) s + logDeriv (NumberField.dedekindZeta K) s := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have hh : s = 1 := sub_eq_zero.mp h
    simp [hh] at hs
  have hd : (mixedDiscriminantScale K : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mixedDiscriminantScale_pos K).ne'
  have hdp : (mixedDiscriminantScale K : ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hd)
  have hg : mixedGammaFactor K s ≠ 0 :=
    mixedGammaFactor_ne_zero K (zero_lt_one.trans hs)
  have hdc : DifferentiableAt ℂ (fun z : ℂ => (mixedDiscriminantScale K : ℂ)^z) s :=
    differentiableAt_id.const_cpow (Or.inl hd)
  have hdg := mixedGammaFactor_differentiableAt K (zero_lt_one.trans hs)
  have hdz := (dedekindZeta_analyticOnNhd K s hs).differentiableAt
  have he : mixedCompletedDedekindXi K =ᶠ[𝓝 s]
      (fun z => z * (z - 1) * (mixedDiscriminantScale K : ℂ)^z *
        mixedGammaFactor K z * NumberField.dedekindZeta K z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact mixedCompletedDedekindXi_eq K hz
  rw [(logDeriv_congr_nhds he).eq_of_nhds]
  rw [logDeriv_fun_mul
      (f := fun z : ℂ => z * (z - 1) * (mixedDiscriminantScale K : ℂ)^z * mixedGammaFactor K z)
      (g := NumberField.dedekindZeta K) s (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1) hdp) hg)
      hz (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hdc).mul hdg) hdz,
    logDeriv_fun_mul
      (f := fun z : ℂ => z * (z - 1) * (mixedDiscriminantScale K : ℂ)^z)
      (g := mixedGammaFactor K) s (mul_ne_zero (mul_ne_zero hs0 hs1) hdp) hg
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hdc) hdg,
    logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1))
      (g := fun z : ℂ => (mixedDiscriminantScale K : ℂ)^z) s (mul_ne_zero hs0 hs1) hdp
      (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hdc,
    logDeriv_fun_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1)
      s hs0 hs1 differentiableAt_id (differentiableAt_id.sub_const 1),
    logDeriv_id', Complex.logDeriv_const_cpow hd]
  have hsub : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply, ((hasDerivAt_id' s).sub_const 1).deriv]
  rw [hsub, ← Complex.ofReal_log (mixedDiscriminantScale_pos K).le]

end ArtinMatthews.VaryingKummerAnalytic
