module

public import ArtinMatthews.ShiftedVoronoiNormalizedInversion
public import ArtinMatthews.ShiftedVoronoiBesselInversion
public import Mathlib.Analysis.Analytic.Uniqueness


set_option backward.privateInPublic true
@[expose] public section

/-!
# Right-half-plane Mellin inversion for the weight-one Bessel transform

Analytic uniqueness extends the previously proved strip identity to every
positive real part. The reciprocal Gamma factor is entire, including at its
zeros. Polynomial Gamma bounds and arbitrary compact-source Mellin decay then
justify inversion on every positive vertical line.

The analytic-continuation argument and Gamma quotient estimate adapt the
proved calculations in OAI's `DirichletL/Detector/RadialMellin.lean` without
importing its broad `Foundation` dependency.
-/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open OAI.EisensteinSchwartzPoisson OAI.CubicReflectionKernel
open scoped Topology ContDiff

namespace ArtinMatthews

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


private theorem radial_mellin_differentiableAt (W : SchwartzMap ℝ ℂ)
    (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (paperRadialFourier W)) s := by
  obtain ⟨A, hA⟩ := exists_nat_gt s.re
  exact mellin_differentiableAt_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hs

/-- The normalized transform has a holomorphic Mellin transform throughout
its natural right half-plane. -/
theorem normalizedRadialFourier_mellin_differentiableAt
    (W : SchwartzMap ℝ ℂ) (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (normalizedRadialFourier W)) s := by
  have hci : 0 < 1 / radialFourierConstant ^ 2 := by
    exact one_div_pos.mpr (sq_pos_of_pos radialFourierConstant_pos)
  have hfun : normalizedRadialFourier W = fun y =>
      ((1 / radialFourierConstant : ℝ) : ℂ) •
        paperRadialFourier W ((1 / radialFourierConstant ^ 2) * y) := by
    funext y
    simp only [normalizedRadialFourier, smul_eq_mul]
    congr 2
    ring
  have hm : mellin (normalizedRadialFourier W) = fun z =>
      ((1 / radialFourierConstant : ℝ) : ℂ) *
        (((1 / radialFourierConstant ^ 2 : ℝ) : ℂ) ^ (-z) *
          mellin (paperRadialFourier W) z) := by
    funext z
    rw [hfun, mellin_const_smul, mellin_comp_mul_left _ _ hci]
    rfl
  rw [hm]
  apply DifferentiableAt.const_mul
  exact ((differentiableAt_id.neg).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hci.ne'))).mul
      (radial_mellin_differentiableAt W s hs)

/-- The Gamma multiplier identity holds at every positive real part, including
positive integers where the reciprocal denominator vanishes. -/
theorem normalizedRadialFourier_mellin_right
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (s : ℂ) (hs : 0 < s.re) :
    mellin (normalizedRadialFourier W) s =
      (Complex.Gamma s / Complex.Gamma (1 - s)) * mellin W (1 - s) := by
  let D : Set ℂ := {z | 0 < z.re}
  let G : ℂ → ℂ := fun z =>
    (Complex.Gamma z / Complex.Gamma (1 - z)) * mellin W (1 - z)
  have hop : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hcv : Convex ℝ D := (convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have hf : AnalyticOnNhd ℂ (mellin (normalizedRadialFourier W)) D := by
    apply DifferentiableOn.analyticOnNhd _ hop
    intro z hz
    exact (normalizedRadialFourier_mellin_differentiableAt W z hz).differentiableWithinAt
  have hG : DifferentiableOn ℂ G D := by
    intro z hz
    have h1 := Gamma_differentiableAt_of_re_pos z hz
    have h2 := (Complex.differentiable_one_div_Gamma (1 - z)).comp z
      (differentiableAt_const _ |>.sub differentiableAt_id)
    have h3 := (compact_source_mellin_differentiable W a b ha hW
      (W.smooth ⊤) (1 - z)).comp z
        (differentiableAt_const _ |>.sub differentiableAt_id)
    simpa only [G, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using!
      ((h1.mul h2).mul h3).differentiableWithinAt
  have hev : mellin (normalizedRadialFourier W) =ᶠ[𝓝 (1 / 2 : ℂ)] G := by
    have hstrip : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hstrip.mem_nhds (by norm_num)] with z hz
    exact normalizedRadialFourier_mellin W a b ha hW z hz.1 hz.2
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hop)
    hcv.isPreconnected (by norm_num [D]) hev hs

private theorem gamma_quotient_strip (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ (n : ℕ) (C : ℝ), 0 < C ∧ ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      ‖Complex.Gamma ((σ : ℂ) + t * Complex.I) /
        Complex.Gamma (1 - ((σ : ℂ) + t * Complex.I))‖ ≤
          C * (1 + |t|) ^ n := by
  obtain ⟨A, hA⟩ := exists_nat_gt hi
  obtain ⟨C, hC, hb⟩ := Gamma_pair_strip_bound 1 (by norm_num) A
  refine ⟨2 * A + 2, C / lo, div_pos hC hlo, ?_⟩
  intro σ hσ t
  have hσ0 : 0 < σ := hlo.trans_le hσ.1
  have hz : (σ : ℂ) + t * Complex.I ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hh
    linarith
  have hh := hb σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
  norm_num only [Complex.ofReal_one] at hh
  rw [add_comm (1 : ℂ), Complex.Gamma_add_one _ hz, mul_div_assoc, norm_mul] at hh
  have hnorm : lo ≤ ‖(σ : ℂ) + t * Complex.I‖ := by
    apply hσ.1.trans
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using
      Complex.re_le_norm ((σ : ℂ) + t * Complex.I)
  have hh' := (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlo).mpr
  simpa [div_mul_eq_mul_div, mul_comm] using hh'

/-- Arbitrary polynomial decay of the Mellin transform uniformly on compact
vertical strips in the right half-plane. -/
theorem normalizedRadialFourier_mellin_strip_decay
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0 < lo) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ N *
        ‖mellin (normalizedRadialFourier W) ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨n, Cg, hCg, hg⟩ := gamma_quotient_strip lo hi hlo
  obtain ⟨Cw, hCw, hw⟩ := compact_source_mellin_strip_decay W a b ha hW
    (W.smooth ⊤) (1 - hi) (1 - lo) (n + N)
  refine ⟨Cg * Cw, mul_pos hCg hCw, ?_⟩
  intro σ hσ t
  have hwb := hw (1 - σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-t)
  rw [abs_neg, show ((1 - σ : ℝ) : ℂ) + (-t : ℝ) * Complex.I =
      1 - ((σ : ℂ) + t * Complex.I) by push_cast; ring] at hwb
  rw [normalizedRadialFourier_mellin_right W a b ha hW _
    (by simpa using hlo.trans_le hσ.1), norm_mul]
  calc
    _ ≤ (1 + |t|) ^ N * (Cg * (1 + |t|) ^ n *
        ‖mellin W (1 - ((σ : ℂ) + t * Complex.I))‖) := by
      gcongr
      exact hg σ hσ t
    _ = Cg * ((1 + |t|) ^ (n + N) *
        ‖mellin W (1 - ((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ Cg * Cw := mul_le_mul_of_nonneg_left hwb hCg.le

/-- Absolute vertical convergence, proved for every positive abscissa. -/
theorem normalizedRadialFourier_mellin_vertical_integrable_right
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (mellin (normalizedRadialFourier W)) σ := by
  obtain ⟨C, _, hC⟩ := normalizedRadialFourier_mellin_strip_decay W a b ha hW σ σ hσ 2
  have hc : Continuous (fun t : ℝ => mellin (normalizedRadialFourier W)
      ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (normalizedRadialFourier_mellin_differentiableAt W _
      (by simpa using hσ)).continuousAt.comp (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [div_eq_mul_inv] using
      weighted_two_to_cauchy (norm_nonneg _) t (hC σ ⟨le_rfl, le_rfl⟩ t)

/-- Mellin inversion at every positive abscissa. -/
theorem normalizedRadialFourier_mellin_inversion_right
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ)
    (hσ : 0 < σ) (hx : 0 < x) :
    mellinInv σ (mellin (normalizedRadialFourier W)) x = normalizedRadialFourier W x :=
  mellinInv_mellin_eq σ (normalizedRadialFourier W) hx
    (normalizedRadialFourier_mellinConvergent W σ hσ)
    (normalizedRadialFourier_mellin_vertical_integrable_right W a b ha hW σ hσ)
    (normalizedRadialFourier_continuous W).continuousAt

/-- The Gamma quotient inversion remains valid on any line right of zero. -/
theorem normalizedRadialFourier_gamma_mellin_inversion_right
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ)
    (hσ : 0 < σ) (hx : 0 < x) :
    mellinInv σ (fun s => (Complex.Gamma s / Complex.Gamma (1 - s)) *
      mellin W (1 - s)) x = normalizedRadialFourier W x := by
  rw [← normalizedRadialFourier_mellin_inversion_right W a b ha hW σ x hσ hx]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [normalizedRadialFourier_mellin_right W a b ha hW _ (by simpa using hσ)]

/-- The actual Bessel transform has the same Mellin multiplier throughout the
right half-plane. -/
theorem besselZeroTransform_mellin_right
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (s : ℂ) (hs : 0 < s.re) :
    mellin (besselZeroTransform W) s =
      (Complex.Gamma s / Complex.Gamma (1 - s)) * mellin W (1 - s) := by
  rw [mellin_besselZeroTransform_eq_normalizedRadialFourier W a b ha hW]
  exact normalizedRadialFourier_mellin_right W a b ha hW s hs

/-- The actual Bessel inversion formula on every positive vertical line. -/
theorem besselZeroTransform_gamma_inversion_right
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ)
    (hσ : 0 < σ) (hx : 0 < x) :
    mellinInv σ (fun s => (Complex.Gamma s / Complex.Gamma (1 - s)) *
      mellin W (1 - s)) x = besselZeroTransform W x := by
  rw [normalizedRadialFourier_gamma_mellin_inversion_right W a b ha hW σ x hσ hx]
  exact (besselZeroTransform_eq_normalizedRadialFourier_of_positive_support
    W a b ha hW hx).symm

/-- The exact weight-one normalization, valid also on lines with `σ > 1`. -/
theorem weightOneBesselTransform_gamma_inversion_right
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ y : ℝ)
    (hσ : 0 < σ) (hy : 0 < y) :
    weightOneBesselTransform W y = ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      mellinInv σ (fun s => (Complex.Gamma s / Complex.Gamma (1 - s)) *
        mellin W (1 - s)) (4 * Real.pi ^ 2 * y) := by
  rw [besselZeroTransform_gamma_inversion_right W a b ha hW σ _ hσ (by positivity)]
  exact weightOneBesselTransform_eq_besselZeroTransform W y

/-- The right-half-plane formula for an arbitrary smooth compact test,
without requiring a prepackaged Schwartz function. -/
theorem weightOneBesselTransform_gamma_inversion_right_of_smooth_compact
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (a b : ℝ) (ha : 0 < a)
    (hHs : Function.support H ⊆ Icc a b) (σ y : ℝ)
    (hσ : 0 < σ) (hy : 0 < y) :
    weightOneBesselTransform H y = ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      mellinInv σ (fun s => (Complex.Gamma s / Complex.Gamma (1 - s)) *
        mellin H (1 - s)) (4 * Real.pi ^ 2 * y) := by
  have hK : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hHs
  exact weightOneBesselTransform_gamma_inversion_right
    (hK.toSchwartzMap hH) a b ha hHs σ y hσ hy

end ArtinMatthews
