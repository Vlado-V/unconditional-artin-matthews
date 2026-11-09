module

public import ArtinMatthews.SpectralProbeMellin
public import ArtinMatthews.SpectralEisensteinCriticalLine
public import Mathlib.Analysis.Analytic.Order


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed real bump has a nonzero entire Mellin transform. Its
critical zeros and the two-dilate degeneracies form null sets. -/
noncomputable section
open Set Filter MeasureTheory
namespace ArtinMatthews

theorem spectralEntire_critical_nonzero_ae (F : ℂ → ℂ)
    (hF : ∀ s,AnalyticAt ℂ F s) {s₀ : ℂ} (h₀ : F s₀≠0) :
    ∀ᵐ t : ℝ ∂volume,F (eisensteinCriticalPoint t)≠0 := by
  have hA : AnalyticOnNhd ℂ F univ := fun s _ => hF s
  have hD := hA.preimage_zero_mem_codiscrete h₀
  have hL : IsLindelof (F ⁻¹' {0}) := isLindelof_iff_lindelofSpace.mpr inferInstance
  have hc : (F ⁻¹' {0}).Countable := hL.countable_of_isDiscrete (by
    simpa only [preimage_compl,compl_compl] using (mem_codiscrete'.mp hD).2)
  have hp := hc.preimage eisensteinCriticalPoint_injective
  have hz := hp.measure_zero volume
  change volume {t : ℝ | F (eisensteinCriticalPoint t)=0}=0 at hz
  exact ae_iff.mpr (by simpa only [not_ne_iff] using hz)

theorem gamma0ProbeMellin_zero :
    gamma0ProbeMellin 0=((∫ y,gamma0ResidualProbeWeight 0 y):ℝ) := by
  rw [gamma0ProbeMellin_integral]
  have he (y : ℝ) : spectralBoundedExponential gamma0ProbeMellinLog 0 y*gamma0ProbeMellinWeight y=
      (gamma0ResidualProbeWeight 0 y:ℂ) := by
    rw [spectralBoundedExponential_apply,zero_mul,Complex.exp_zero,one_mul]
    simp only [gamma0ProbeMellinWeight,gamma0ResidualProbeWeight,zero_sub,
      Real.rpow_neg_ofNat,zpow_neg,zpow_ofNat,div_eq_mul_inv]
  simp_rw [he]
  exact integral_ofReal

theorem gamma0ProbeMellin_zero_ne : gamma0ProbeMellin 0≠0 := by
  rw [gamma0ProbeMellin_zero]
  exact Complex.ofReal_ne_zero.mpr (gamma0ResidualProbeWeight_pos_integral 0).ne'

theorem gamma0ProbeMellin_critical_nonzero_ae :
    ∀ᵐ t : ℝ ∂volume,gamma0ProbeMellin (eisensteinCriticalPoint t)≠0 :=
  spectralEntire_critical_nonzero_ae gamma0ProbeMellin gamma0ProbeMellin_analyticAt gamma0ProbeMellin_zero_ne

def gamma0ProbeDilationDifference (s : ℂ) : ℂ := (2:ℂ)^(s-1)-(2:ℂ)^(-s)

theorem gamma0ProbeDilationDifference_analyticAt (s : ℂ) :
    AnalyticAt ℂ gamma0ProbeDilationDifference s := by
  have h2 : (2:ℂ)≠0 := by norm_num
  have he : gamma0ProbeDilationDifference=(fun z : ℂ =>
      Complex.exp (Complex.log 2*(z-1))-Complex.exp (Complex.log 2*(-z))) := by
    funext z
    simp only [gamma0ProbeDilationDifference,Complex.cpow_def_of_ne_zero h2]
  rw [he]
  apply Differentiable.analyticAt
  fun_prop

theorem gamma0ProbeDilationDifference_one_ne : gamma0ProbeDilationDifference 1≠0 := by
  norm_num [gamma0ProbeDilationDifference,Complex.cpow_neg_one]

theorem gamma0ProbeDilationDifference_critical_nonzero_ae :
    ∀ᵐ t : ℝ ∂volume,gamma0ProbeDilationDifference (eisensteinCriticalPoint t)≠0 :=
  spectralEntire_critical_nonzero_ae gamma0ProbeDilationDifference
    gamma0ProbeDilationDifference_analyticAt gamma0ProbeDilationDifference_one_ne

end ArtinMatthews
