module

public import ArtinMatthews.SourceComplexUnitHaar
public import ArtinMatthews.SourceComplexMellinWeight
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import ArtinMatthews.SourceComplexMellinAbsolute
public import ArtinMatthews.SourceComplexMellinNormalized
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set Filter
open ArtinMatthews.VaryingKummerAnalytic
open scoped ENNReal SchwartzMap
noncomputable section

def sourceComplexNormDensity (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖z‖ ^ 2)⁻¹)

def sourceComplexUnitMellinIntegrand (g : ℂ → ℂ) (s : ℂ) (z : ℂ) : ℂ :=
  g z * (((‖z‖ ^ 2 : ℝ) : ℂ) ^ s)

theorem sourceComplexNormDensity_measurable : Measurable sourceComplexNormDensity := by
  unfold sourceComplexNormDensity
  fun_prop

theorem sourceComplexUnitMellinIntegrand_measurable (g : 𝓢(ℂ, ℂ)) (s : ℂ) :
    Measurable (sourceComplexUnitMellinIntegrand g s) := by
  apply g.continuous.measurable.mul
  have he : Measurable (fun z : ℂ => Complex.exp ((Real.log (‖z‖ ^ 2) : ℂ) * s)) :=
    Complex.continuous_exp.measurable.comp ((Complex.continuous_ofReal.measurable.comp
      (Real.measurable_log.comp (by fun_prop))).mul_const s)
  have hp : Measurable (fun z : ℂ => if z = 0 then (0 : ℂ) ^ s else
      Complex.exp ((Real.log (‖z‖ ^ 2) : ℂ) * s)) :=
    measurable_const.ite (measurableSet_singleton (0 : ℂ)) he
  convert hp using 1
  funext z
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))),
      ← Complex.ofReal_log (by positivity)]

theorem sourceComplexNormDensity_smul_integrand (g : ℂ → ℂ) (s z : ℂ) (hz : z ≠ 0) :
    (sourceComplexNormDensity z).toReal • sourceComplexUnitMellinIntegrand g s z =
      g z * sourceComplexMellinWeight s z := by
  rw [sourceComplexNormDensity, ENNReal.toReal_ofReal (by positivity),
    sourceComplexMellinWeight_eq_normalized s z hz, sourceComplexUnitMellinIntegrand]
  rw [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ac_rfl

theorem sourceComplexUnitMellinIntegrand_integrable (g : 𝓢(ℂ, ℂ)) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun z : ℂˣ => sourceComplexUnitMellinIntegrand g s z) sourceComplexUnitHaar := by
  have h : Integrable (sourceComplexUnitMellinIntegrand g s)
      (sourceComplexTraceMeasure.withDensity sourceComplexNormDensity) := by
    apply (integrable_withDensity_iff_integrable_smul' sourceComplexNormDensity_measurable
      (Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))).mpr
    apply (sourceComplexMellin_integrable g s hs).congr
    filter_upwards [sourceComplexTraceMeasure_ae_ne_zero] with z hz
    exact (sourceComplexNormDensity_smul_integrand g s z hz).symm
  unfold sourceComplexNormDensity at h
  rw [← sourceComplexUnitHaar_map_val] at h
  exact h.comp_measurable Units.continuous_val.measurable

theorem sourceComplexUnitMellinIntegrand_norm (g : 𝓢(ℂ, ℂ)) (s : ℂ) (z : ℂˣ) :
    ‖sourceComplexUnitMellinIntegrand g s z‖ =
      ‖g z‖ * (‖(z : ℂ)‖ ^ 2) ^ s.re := by
  rw [sourceComplexUnitMellinIntegrand, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos (norm_pos_iff.mpr z.ne_zero) _)]

theorem sourceComplexUnitHaar_weighted_norm_integrable (g : 𝓢(ℂ, ℂ)) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun z : ℂˣ => ‖g z‖ * (‖(z : ℂ)‖ ^ 2) ^ σ) sourceComplexUnitHaar := by
  refine (sourceComplexUnitMellinIntegrand_integrable g (σ : ℂ) hσ).norm.congr ?_
  filter_upwards with z
  exact sourceComplexUnitMellinIntegrand_norm g (σ : ℂ) z

end
end ArtinMatthews.SourcePhysical
