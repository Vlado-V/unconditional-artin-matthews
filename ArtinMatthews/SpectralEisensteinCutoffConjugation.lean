module

public import ArtinMatthews.SpectralEisensteinTruncatedPairFlux


set_option backward.privateInPublic true
@[expose] public section

/-! Real cusp cutoffs and their genuine radial errors respect
conjugation of the spectral exponent. -/
noncomputable section
open scoped ContDiff
namespace ArtinMatthews

theorem spectralCpow_conj_real_nonneg (q : ℂ) {t : ℝ} (ht : 0≤t) :
    (t:ℂ)^((starRingEnd ℂ) q)=(starRingEnd ℂ) ((t:ℂ)^q) := by
  rw [Complex.cpow_conj _ _ (by rw [Complex.arg_ofReal_of_nonneg ht];exact Real.pi_ne_zero.symm),
    Complex.conj_ofReal]

theorem spectralDeriv_conjugate (f : ℝ → ℂ) (hf : Differentiable ℝ f) :
    deriv (fun t => (starRingEnd ℂ) (f t))=fun t => (starRingEnd ℂ) (deriv f t) := by
  funext t
  exact (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t ((hf t).hasDerivAt)).deriv

theorem eisensteinVerticalCutoffMode_conj (s : ℂ) :
    eisensteinVerticalCutoffMode ((starRingEnd ℂ) s)=fun t => (starRingEnd ℂ) (eisensteinVerticalCutoffMode s t) := by
  funext t
  by_cases ht : 0≤t
  · rw [eisensteinVerticalCutoffMode,eisensteinVerticalCutoffMode,spectralCpow_conj_real_nonneg s ht,
      map_mul,Complex.conj_ofReal]
  · have ht' : t≤1 := by linarith [lt_of_not_ge ht]
    rw [eisensteinVerticalCutoffMode_zero _ ht',eisensteinVerticalCutoffMode_zero _ ht',map_zero]

theorem eisensteinVerticalCutoffError_conj (s : ℂ) (t : ℝ) :
    eisensteinVerticalCutoffError ((starRingEnd ℂ) s) t=(starRingEnd ℂ) (eisensteinVerticalCutoffError s t) := by
  let f := eisensteinVerticalCutoffMode s
  have hf : ContDiff ℝ ∞ f := eisensteinVerticalCutoffMode_smooth s
  have hd := spectralDeriv_conjugate f (hf.differentiable (by simp))
  have hdd := spectralDeriv_conjugate (deriv f) ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp))
  have hm : eisensteinVerticalCutoffMode ((starRingEnd ℂ) s)=fun y => (starRingEnd ℂ) (f y) :=
    eisensteinVerticalCutoffMode_conj s
  unfold eisensteinVerticalCutoffError
  change -((t:ℂ)^2)*deriv (deriv (eisensteinVerticalCutoffMode ((starRingEnd ℂ) s))) t-
    (starRingEnd ℂ) s*(1-(starRingEnd ℂ) s)*eisensteinVerticalCutoffMode ((starRingEnd ℂ) s) t=
      (starRingEnd ℂ) (-((t:ℂ)^2)*deriv (deriv f) t-s*(1-s)*f t)
  rw [hm,hd,hdd]
  simp only [map_sub,map_mul,map_neg,map_pow,Complex.conj_ofReal,map_one]

theorem eisensteinOutgoingApprox_conj (s : ℂ) (A : ℝ) {t : ℝ} (ht : 0≤t) :
    eisensteinOutgoingApprox ((starRingEnd ℂ) s) A t=(starRingEnd ℂ) (eisensteinOutgoingApprox s A t) := by
  simp only [eisensteinOutgoingApprox,spectralCpow_conj_real_nonneg s ht,map_mul,Complex.conj_ofReal]

theorem eisensteinUpperCutoffError_conj (s : ℂ) {A : ℝ} (hA : 0≤A) (t : ℝ) :
    eisensteinUpperCutoffError ((starRingEnd ℂ) s) A t=(starRingEnd ℂ) (eisensteinUpperCutoffError s A t) := by
  simp only [eisensteinUpperCutoffError,← map_neg (starRingEnd ℂ) s,
    spectralCpow_conj_real_nonneg (-s) hA,eisensteinVerticalCutoffError_conj,map_mul]

end ArtinMatthews
