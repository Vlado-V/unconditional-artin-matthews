module

public import ArtinMatthews.SpectralKAdjacentOrderMoment
public import ArtinMatthews.SpectralCuspInteriorParseval


set_option backward.privateInPublic true
@[expose] public section

/-! A quantitative Fourier truncation on a finite interval. The
derivative estimate follows by integration by parts with matching
endpoint values, and Parseval controls the discarded modes. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators

namespace ArtinMatthews

theorem spectral_fourierCoeffOn_phase_integral {L : ℝ} (hL : 0 < L)
    (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn hL f n = (L : ℂ)⁻¹*∫ x in (0 : ℝ)..L, cuspFourierPhase L n x*f x := by
  rw [fourierCoeffOn_eq_integral]
  simp_rw [← cuspFourierPhase_eq_addCircle_fourier (L-0) (by simpa using hL) n]
  simp only [sub_zero,Complex.real_smul,one_div,smul_eq_mul,Complex.ofReal_inv]

theorem spectral_fourierCoeffOn_deriv_of_endpoints {L : ℝ} (hL : 0 < L)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (he : f L = f 0) (n : ℤ) :
    fourierCoeffOn hL (deriv f) n =
      (((cuspFourierFrequency L n : ℝ) : ℂ)*Complex.I)*fourierCoeffOn hL f n := by
  have hφ := cuspFourierPhase_contDiff L n
  have hd := hf.continuous_deriv (by simp)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => cuspFourierPhase_hasDerivAt L n x)
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
    ((hφ.continuous.mul continuous_const).intervalIntegrable 0 L)
    (hd.intervalIntegrable 0 L)
  rw [cuspFourierPhase_period L hL n,cuspFourierPhase_zero,one_mul,one_mul,he,sub_self,zero_sub] at hi
  have hfactor :
      (∫ x in (0 : ℝ)..L, (cuspFourierPhase L n x*
        (-((cuspFourierFrequency L n : ℝ) : ℂ)*Complex.I))*f x) =
      (-((cuspFourierFrequency L n : ℝ) : ℂ)*Complex.I)*
        (∫ x in (0 : ℝ)..L, cuspFourierPhase L n x*f x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hfactor] at hi
  have hIBP :
      (∫ x in (0 : ℝ)..L, cuspFourierPhase L n x*deriv f x) =
      (((cuspFourierFrequency L n : ℝ) : ℂ)*Complex.I)*
        (∫ x in (0 : ℝ)..L, cuspFourierPhase L n x*f x) := by
    simpa only [neg_mul,neg_neg] using hi
  rw [spectral_fourierCoeffOn_phase_integral hL (deriv f) n,spectral_fourierCoeffOn_phase_integral hL f n,hIBP]
  ring

theorem spectral_fourierCoeffOn_energy_truncation {L : ℝ} (hL : 0 < L)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (he : f L = f 0)
    (s : Finset ℤ) {D : ℝ} (hD : 0 < D)
    (hcut : ∀ n : ℤ, n ∉ s → D ≤ |cuspFourierFrequency L n|) :
    L⁻¹*(∫ x in (0 : ℝ)..L, ‖f x‖^2) ≤
      (∑ n ∈ s, ‖fourierCoeffOn hL f n‖^2)+
        (D^2)⁻¹*(L⁻¹*(∫ x in (0 : ℝ)..L, ‖deriv f x‖^2)) := by
  let A (n : ℤ) := ‖fourierCoeffOn hL f n‖^2
  let B (n : ℤ) := ‖fourierCoeffOn hL (deriv f) n‖^2
  let S := ((s : Set ℤ)ᶜ)
  have hmem (g : ℝ → ℂ) (hg : Continuous g) : MemLp g 2 (volume.restrict (Ioc 0 L)) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
      ((hg.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hA : HasSum A (L⁻¹*(∫ x in (0 : ℝ)..L, ‖f x‖^2)) := by
    simpa only [sub_zero,smul_eq_mul] using hasSum_sq_fourierCoeffOn hL (hmem f hf.continuous)
  have hB : HasSum B (L⁻¹*(∫ x in (0 : ℝ)..L, ‖deriv f x‖^2)) := by
    simpa only [sub_zero,smul_eq_mul] using
      hasSum_sq_fourierCoeffOn hL (hmem (deriv f) (hf.continuous_deriv (by simp)))
  have hBnorm (n : ℤ) : B n = |cuspFourierFrequency L n|^2*A n := by
    unfold A B
    rw [spectral_fourierCoeffOn_deriv_of_endpoints hL f hf he,norm_mul,norm_mul,Complex.norm_real,
      Complex.norm_I,mul_one,mul_pow,Real.norm_eq_abs]
  have hp (n : S) : A n.val ≤ (D^2)⁻¹*B n.val := by
    rw [hBnorm,← div_eq_inv_mul]
    apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
    have h := hcut n.val n.property
    calc
      _ ≤ A n.val*|cuspFourierFrequency L n.val|^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD.le h 2) (sq_nonneg _)
      _ = _ := mul_comm _ _
  have hAs : Summable (fun n : S => A n.val) := hA.summable.subtype S
  have hBs : Summable (fun n : S => B n.val) := hB.summable.subtype S
  have htail : (∑' n : S, A n.val) ≤ ∑' n : S, (D^2)⁻¹*B n.val :=
    hAs.tsum_le_tsum hp (hBs.mul_left (D^2)⁻¹)
  rw [tsum_mul_left] at htail
  have htotal : (∑' n : S, B n.val) ≤ L⁻¹*(∫ x in (0 : ℝ)..L, ‖deriv f x‖^2) :=
    (Summable.tsum_subtype_le B S (fun _ => sq_nonneg _) hB.summable).trans_eq hB.tsum_eq
  have hsplit : (∑ n ∈ s, A n)+(∑' n : S, A n.val) = L⁻¹*(∫ x in (0 : ℝ)..L, ‖f x‖^2) :=
    (hA.summable.sum_add_tsum_compl (s := s)).trans hA.tsum_eq
  rw [← hsplit]
  exact add_le_add le_rfl (htail.trans (mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr (sq_nonneg _))))

end ArtinMatthews
