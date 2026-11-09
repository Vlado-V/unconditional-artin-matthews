module

public import ArtinMatthews.SpectralEisensteinProfileChannels
public import ArtinMatthews.SpectralProbeMellinNonvanishing


set_option backward.privateInPublic true
@[expose] public section

/-! Two genuine high cusp-profile dilates separate incoming amplitudes.
The resulting completed Eisenstein synthesis has zero kernel. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

theorem spectralTwoDilate_separation {c : ℝ} (hc : 0<c) (s m e z : ℂ)
    (hm : m≠0) (hd : gamma0ProbeDilationDifference s≠0)
    (h1 : (c:ℂ)^(s-1)*m*z+(c:ℂ)^(-s)*e=0)
    (h2 : ((2*c:ℝ):ℂ)^(s-1)*m*z+((2*c:ℝ):ℂ)^(-s)*e=0) : z=0 := by
  have hp (q : ℂ) : ((2*c:ℝ):ℂ)^q=(2:ℂ)^q*(c:ℂ)^q := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by norm_num) hc.le q
  rw [hp,hp] at h2
  have he : gamma0ProbeDilationDifference s*((c:ℂ)^(s-1)*m*z)=0 := by
    unfold gamma0ProbeDilationDifference
    linear_combination h2-(2:ℂ)^(-s)*h1
  have hc' : (c:ℂ)^(s-1)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hd)).resolve_left (mul_ne_zero hc' hm)

theorem gamma0EisensteinSynthesis_kernel_zero (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) (hv : (gamma0EisensteinAnalysis N).adjoint v=0) : v=0 := by
  let c := gamma0EisensteinMatchingHeight N
  have hc : 0<c := gamma0EisensteinMatchingHeight_pos N
  have hc2 : 0<2*c := mul_pos (by norm_num) hc
  have hH2 : gamma0EisensteinMatchingHeight N≤2*c := by change c≤2*c;linarith
  have hI : ∀ᵐ t ∂gamma0EisensteinSpectralMeasure,gamma0ProbeMellin (eisensteinCriticalPoint t)≠0 := by
    change ∀ᵐ t ∂(ENNReal.ofReal ((2*Real.pi)⁻¹) • volume.restrict (Ioi 0)),_
    exact Measure.ae_smul_measure (ae_restrict_of_ae gamma0ProbeMellin_critical_nonzero_ae) _
  have hD : ∀ᵐ t ∂gamma0EisensteinSpectralMeasure,gamma0ProbeDilationDifference (eisensteinCriticalPoint t)≠0 := by
    change ∀ᵐ t ∂(ENNReal.ofReal ((2*Real.pi)⁻¹) • volume.restrict (Ioi 0)),_
    exact Measure.ae_smul_measure (ae_restrict_of_ae gamma0ProbeDilationDifference_critical_nonzero_ae) _
  apply PiLp.ext
  intro i
  change v i=0
  apply Lp.ext
  have h1 := gamma0EisensteinSynthesis_kernel_profile_equation N v hv i hc le_rfl
  have h2 := gamma0EisensteinSynthesis_kernel_profile_equation N v hv i hc2 hH2
  filter_upwards [h1,h2,hI,hD,Lp.coeFn_zero ℂ 2 gamma0EisensteinSpectralMeasure] with t ht1 ht2 hi hd hz
  have he : v i t=0 := by
    let s := eisensteinCriticalPoint t
    let E := gamma0ProbeMellin (1-s)*
      (∑ j : Gamma0EisensteinCuspClasses N,
        gamma0EisensteinMatchedCoefficient N (gamma0EisensteinCuspClassRepresentative N j) s i*v j t)
    apply spectralTwoDilate_separation hc s (gamma0ProbeMellin s) E (v i t) hi hd
    · simpa only [E,s,mul_assoc] using ht1
    · simpa only [E,s,mul_assoc] using ht2
  exact he.trans hz.symm

theorem gamma0EisensteinSynthesis_injective (N : ℕ) [NeZero N] :
    Function.Injective (gamma0EisensteinAnalysis N).adjoint := by
  intro v w h
  have hz : (gamma0EisensteinAnalysis N).adjoint (v-w)=0 := by rw [map_sub,h,sub_self]
  exact sub_eq_zero.mp (gamma0EisensteinSynthesis_kernel_zero N (v-w) hz)

end ArtinMatthews
