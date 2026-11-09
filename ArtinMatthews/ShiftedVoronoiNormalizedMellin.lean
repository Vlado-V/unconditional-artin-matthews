module

public import ArtinMatthews.ShiftedVoronoiRadialNormalization
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Mellin transform of the normalized radial Fourier operator

The absolute Fubini argument adapts the proved Laplace/Mellin calculations in
`OAI/NumberTheory/DirichletL/Detector/RadialMellin.lean`. The compact-source
convergence proof adapts `DirichletL/Mellin/ReflectedKernel.lean`.
No `DirichletL.Foundation` import or assumed transform formula is used.
-/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open OAI.EisensteinSchwartzPoisson
open scoped Topology

namespace ArtinMatthews

private lemma mellinConvergent_real (f : ℝ → ℂ) (s : ℝ) :
    MellinConvergent f (s : ℂ) ↔
      IntegrableOn (fun r : ℝ => (r^(s-1) : ℝ) • f r) (Ioi 0) := by
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

private lemma gamma_scaled_integrable {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    IntegrableOn (fun t : ℝ => t^(s-1)*Real.exp (-(r*t))) (Ioi 0) := by
  have hg : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (s : ℂ) := by
    rw [mellinConvergent_real]
    simpa only [Complex.real_smul, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_mul, mul_comm] using!
      (Real.GammaIntegral_convergent hs).ofReal (𝕜 := ℂ)
  have hh := (MellinConvergent.comp_mul_left (f := fun t : ℝ => (Real.exp (-t) : ℂ))
    (s := (s : ℂ)) hr).mpr hg
  rw [mellinConvergent_real] at hh
  simpa only [RCLike.smul_re, RCLike.ofReal_re] using! hh.re

private lemma gamma_scaled_integral {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    (∫ t : ℝ in Ioi 0, t^(s-1)*Real.exp (-(r*t))) =
      r^(-s)*Real.Gamma s := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr, one_div, Real.inv_rpow hr.le,
    Real.rpow_neg hr.le]

private lemma laplace_mellin_integrable (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    Integrable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    exact hf.comp_fst.mul (by fun_prop)
  have hn (r t : ℝ) (ht : 0<t) :
      ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖ =
        ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t))) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_exp]
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.ofReal_re]
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    apply ((gamma_scaled_integrable hs hr).const_mul ‖f r‖).mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hn r t ht).le
  · have hw : IntegrableOn (fun r : ℝ => r^(-s.re)*‖f r‖) (Ioi 0) := by
      apply hconv.norm.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
        Complex.sub_re, Complex.one_re]
      congr 2
      ring
    apply (hw.const_mul (Real.Gamma s.re)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hi : (fun t : ℝ => ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖) =ᵐ[
      volume.restrict (Ioi 0)] (fun t => ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t)))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hn r t ht
    rw [integral_congr_ae hi]
    rw [integral_const_mul, gamma_scaled_integral hs hr]
    ring

theorem mellin_radialLaplace (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    mellin (radialLaplace f) s = Complex.Gamma s * mellin f (1-s) := by
  have hi := laplace_mellin_integrable f s hs hf hconv
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ r : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) := by
      unfold mellin radialLaplace
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [smul_eq_mul, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [mul_comm r t]
      ring
    _ = ∫ r : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) :=
      integral_integral_swap hi.swap
    _ = ∫ r : ℝ in Ioi 0, f r*((r:ℂ)^(-s)*Complex.Gamma s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [integral_const_mul]
      have hh := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
      simp only [Complex.ofReal_mul] at *
      rw [hh, one_div, Complex.inv_cpow_ofReal_nonneg hr.le, Complex.cpow_neg]
    _ = _ := by
      rw [mellin, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [show 1-s-1 = -s by ring, smul_eq_mul]
      ring


private lemma radial_continuous (W : SchwartzMap ℝ ℂ) : Continuous (paperRadialFourier W) := by
  rw [paperRadialFourier_eq_ray]
  exact (paperFourierRayCLM W).continuous.comp Real.continuous_sqrt

private lemma radial_isBigO_top (W : SchwartzMap ℝ ℂ) (A : ℕ) :
    paperRadialFourier W =O[atTop] (fun r : ℝ => r^(-(A:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W A 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  have hh := hb 0 (by omega) r hr
  simp only [OAI.LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero, mul_one] at hh
  have hp : r^A * ‖paperRadialFourier W r‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le (by linarith : r≤1+r) A)
      (norm_nonneg _)).trans hh
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _),
    Real.rpow_neg hr.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hr A)).mpr (by simpa [mul_comm] using hp)

private lemma radial_isBigO_zero (W : SchwartzMap ℝ ℂ) :
    paperRadialFourier W =O[𝓝[>] 0] (fun r : ℝ => r^(-(0:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W 0 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  simpa [OAI.LocalLogFourier.eulerDeriv] using hb 0 (by omega) r hr

private theorem radial_mellin_convergent (W : SchwartzMap ℝ ℂ) (z : ℂ) (hz : 0<z.re) :
    MellinConvergent (paperRadialFourier W) z := by
  obtain ⟨A, hA⟩ := exists_nat_gt z.re
  exact mellinConvergent_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz


/-- The normalized radial transform has a convergent Mellin integral throughout
its natural right half-plane. -/
theorem normalizedRadialFourier_mellinConvergent (W : SchwartzMap ℝ ℂ)
    (s : ℂ) (hs : 0 < s.re) : MellinConvergent (normalizedRadialFourier W) s := by
  have hci : 0 < 1 / radialFourierConstant ^ 2 := by
    exact one_div_pos.mpr (sq_pos_of_pos radialFourierConstant_pos)
  have hfun : normalizedRadialFourier W = fun y =>
      ((1 / radialFourierConstant : ℝ) : ℂ) •
        paperRadialFourier W ((1 / radialFourierConstant ^ 2) * y) := by
    funext y
    simp only [normalizedRadialFourier, smul_eq_mul]
    congr 2
    ring
  rw [hfun]
  exact ((MellinConvergent.comp_mul_left (f := paperRadialFourier W) (s := s) hci).mpr
    (radial_mellin_convergent W s hs)).const_smul ((1 / radialFourierConstant : ℝ) : ℂ)

private theorem compact_source_mellinConvergent (W : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0 < a) (hW : Function.support W ⊆ Icc a b) (s : ℂ) :
    MellinConvergent W s := by
  have hlocal : LocallyIntegrableOn (W : ℝ → ℂ) (Ioi (0 : ℝ)) :=
    W.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : (W : ℝ → ℂ) =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hW hn).2
  have hbotzero : (W : ℝ → ℂ) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hW hn).1
  have htop : (W : ℝ → ℂ) =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : (W : ℝ → ℂ) =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith) hbot (by linarith)

private theorem mellin_reciprocal_radialLaplace (W : ℝ → ℂ) (s : ℂ) :
    mellin (fun t : ℝ => ((1 / t : ℝ) : ℂ) * radialLaplace W (1 / t)) (1 - s) =
      mellin (radialLaplace W) s := by
  have hfun : (fun t : ℝ => ((1 / t : ℝ) : ℂ) * radialLaplace W (1 / t)) =
      (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ) • radialLaplace W t⁻¹) := by
    funext t
    simp only [Complex.cpow_neg_one, smul_eq_mul, one_div, Complex.ofReal_inv]
  rw [hfun, mellin_cpow_smul, show 1 - s + (-1) = -s by ring,
    mellin_comp_inv, neg_neg]

/-- The full Mellin multiplier of the normalized radial Fourier transform on
compact smooth sources away from zero, with both Mellin integrals justified. -/
theorem normalizedRadialFourier_mellin (W : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0 < a) (hW : Function.support W ⊆ Icc a b)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s.re < 1) :
    mellin (normalizedRadialFourier W) s =
      (Complex.Gamma s / Complex.Gamma (1 - s)) * mellin W (1 - s) := by
  have hc := compact_source_mellinConvergent W a b ha hW (1 - s)
  have hL := mellin_radialLaplace (normalizedRadialFourier W) (1 - s)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (normalizedRadialFourier_continuous W).aestronglyMeasurable
    (by simpa only [sub_sub_cancel] using normalizedRadialFourier_mellinConvergent W s hs)
  have hR := mellin_radialLaplace W s hs W.continuous.aestronglyMeasurable hc
  have he : mellin (radialLaplace (normalizedRadialFourier W)) (1 - s) =
      mellin (fun t : ℝ => ((1 / t : ℝ) : ℂ) * radialLaplace W (1 / t)) (1 - s) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [normalizedRadialFourier_laplace W t ht]
  rw [hL, sub_sub_cancel, mellin_reciprocal_radialLaplace, hR] at he
  have hg : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]; linarith)
  apply mul_left_cancel₀ hg
  rw [he]
  field_simp

end ArtinMatthews
