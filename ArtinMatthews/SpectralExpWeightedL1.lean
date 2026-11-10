module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The exact half-line moments needed to extend the Gaussian test functional. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff Topology
noncomputable section

private theorem exp_sqrt_moment :
    IntegrableOn (fun s : ℝ => Real.exp (-s) / Real.sqrt s) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, Real.exp (-s) / Real.sqrt s) = Real.sqrt Real.pi := by
  have he (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      Real.exp (-s) / Real.sqrt s = s ^ (-(1 / 2) : ℝ) * Real.exp (-s) := by
    have hs₀ : 0 ≤ s := le_of_lt hs
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hs₀, mul_comm]
  have hi : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2) : ℝ) * Real.exp (-s)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := -(1 / 2)) (by norm_num) one_pos
  refine ⟨hi.congr_fun (fun s hs => (he s hs).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he]
  simpa only [one_mul, div_self one_ne_zero, Real.one_rpow, Real.Gamma_one_half_eq,
    show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] using
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := 1) (by norm_num) one_pos

private theorem exp_linear_moment :
    IntegrableOn (fun s : ℝ => (1 + s) * Real.exp (-s)) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, (1 + s) * Real.exp (-s)) = 2 := by
  have hi : IntegrableOn (fun s : ℝ => s * Real.exp (-s)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_rpow (p := 1) (s := 1) (by norm_num) one_pos
  have hi₀ := integrableOn_exp_neg_Ioi 0
  have hΓ : Real.Gamma 2 = 1 := by norm_num
  have hm : (∫ s : ℝ in Ioi 0, s * Real.exp (-s)) = 1 := by
    simpa only [one_mul, div_self one_ne_zero, Real.one_rpow, hΓ,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1) (by norm_num) one_pos
  refine ⟨?_, ?_⟩
  · simpa only [add_mul, one_mul, Pi.add_apply] using! hi₀.add hi
  · simp only [add_mul, one_mul]
    rw [integral_add hi₀ hi, integral_exp_neg_Ioi_zero, hm] <;> norm_num

private theorem spectralL1_envelope_Ioi
    {F K : ℝ → ℝ} (hF : Measurable F) (hK : IntegrableOn K (Ioi 0))
    (hpos : ∀ s : ℝ, 0 < s → 0 ≤ F s) {ε : ℝ}
    (hbound : ∀ s : ℝ, 0 < s → F s ≤ ε * K s) :
    IntegrableOn F (Ioi 0) ∧ (∫ s : ℝ in Ioi 0, F s) ≤ ε * ∫ s : ℝ in Ioi 0, K s := by
  have hK' : IntegrableOn (fun s => ε * K s) (Ioi 0) := hK.const_mul ε
  have hInt : IntegrableOn F (Ioi 0) := by
    apply hK'.mono' hF.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
    have hs' : 0 < s := hs
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos s hs')]
    exact hbound s hs'
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ s : ℝ in Ioi 0, ε * K s :=
      setIntegral_mono_on hInt hK' measurableSet_Ioi hbound
    _ = _ := integral_const_mul ε K

theorem spectralSquareRadialDerivative_eq {d : ℝ → ℂ} (hd : ContDiff ℝ 2 d) (s : ℝ) :
    deriv (fun t : ℝ => (t : ℂ) * deriv d t) s =
      deriv d s + (s : ℂ) * deriv (deriv d) s := by
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := by
    simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id s).ofReal_comp
  simpa only [one_mul] using (hid.fun_mul (hd.differentiable_deriv_two s).hasDerivAt).deriv

theorem spectralExpEnvelope_radial
    {d : ℝ → ℂ} (hd : ContDiff ℝ 2 d) {ε : ℝ}
    (hfirst : ∀ s : ℝ, 0 ≤ s → ‖deriv d s‖ ≤ ε * Real.exp (-s))
    (hsecond : ∀ s : ℝ, 0 ≤ s → ‖deriv (deriv d) s‖ ≤ ε * Real.exp (-s))
    (s : ℝ) (hs : 0 ≤ s) :
    ‖deriv (fun t : ℝ => (t : ℂ) * deriv d t) s‖ ≤ ε * ((1 + s) * Real.exp (-s)) := by
  rw [spectralSquareRadialDerivative_eq hd]
  calc
    _ ≤ ‖deriv d s‖ + s * ‖deriv (deriv d) s‖ := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] using
        norm_add_le (deriv d s) ((s : ℂ) * deriv (deriv d) s)
    _ ≤ ε * Real.exp (-s) + s * (ε * Real.exp (-s)) :=
      add_le_add (hfirst s hs) (mul_le_mul_of_nonneg_left (hsecond s hs) hs)
    _ = _ := by ring

theorem spectralExpEnvelope_weightedL1
    {d : ℝ → ℂ} (hd : ContDiff ℝ 2 d) {ε : ℝ}
    (henv : ∀ s : ℝ, 0 ≤ s →
      ‖d s‖ ≤ ε * Real.exp (-s) ∧
      ‖deriv d s‖ ≤ ε * Real.exp (-s) ∧
      ‖deriv (deriv d) s‖ ≤ ε * Real.exp (-s)) :
    (IntegrableOn (fun s : ℝ => ‖d s‖ / Real.sqrt s) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, ‖d s‖ / Real.sqrt s) ≤ ε * Real.sqrt Real.pi) ∧
    (IntegrableOn (fun s : ℝ => ‖d s‖) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, ‖d s‖) ≤ ε) ∧
    (IntegrableOn (fun s : ℝ => ‖deriv (fun t : ℝ => (t : ℂ) * deriv d t) s‖) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, ‖deriv (fun t : ℝ => (t : ℂ) * deriv d t) s‖) ≤ 2 * ε) := by
  have hnorm := hd.continuous.norm.measurable
  refine ⟨?_, ?_, ?_⟩
  · have hb (s : ℝ) (hs : 0 < s) : ‖d s‖ / Real.sqrt s ≤
        ε * (Real.exp (-s) / Real.sqrt s) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (henv s hs.le).1 (Real.sqrt_nonneg _)
    have hm : Measurable (fun s : ℝ => ‖d s‖ / Real.sqrt s) :=
      hnorm.div Real.continuous_sqrt.measurable
    have he := spectralL1_envelope_Ioi hm exp_sqrt_moment.1
      (fun s _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg s)) hb
    simpa only [exp_sqrt_moment.2] using he
  · have he := spectralL1_envelope_Ioi hnorm (integrableOn_exp_neg_Ioi 0)
      (fun _ _ => norm_nonneg _) (fun s hs => (henv s hs.le).1)
    simpa only [integral_exp_neg_Ioi_zero, mul_one] using he
  · have hd' : ContDiff ℝ 1 (deriv d) := hd.deriv'
    have hflux : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ) * deriv d t) :=
      Complex.ofRealCLM.contDiff.mul hd'
    have hb (s : ℝ) (hs : 0 < s) :
        ‖deriv (fun t : ℝ => (t : ℂ) * deriv d t) s‖ ≤ ε * ((1 + s) * Real.exp (-s)) :=
      spectralExpEnvelope_radial hd (fun t ht => (henv t ht).2.1)
        (fun t ht => (henv t ht).2.2) s hs.le
    have he := spectralL1_envelope_Ioi hflux.continuous_deriv_one.norm.measurable
      exp_linear_moment.1 (fun _ _ => norm_nonneg _) hb
    simpa only [exp_linear_moment.2, mul_comm ε 2] using he

end
end ArtinMatthews
