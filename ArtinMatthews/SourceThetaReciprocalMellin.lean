module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ArtinMatthews.ShiftedVoronoiGammaGrowth
public import ArtinMatthews.VaryingKummerAnalyticGaussianFiniteBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta


set_option backward.privateInPublic true
@[expose] public section

/-! The actual entire reciprocal-Gamma multiplier for source03. Its
Gaussian bound is uniform on every fixed vertical strip. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Complex VaryingKummerAnalytic
noncomputable section

def sourceThetaMellinSymbol (C₀ A₀ : ℝ) (r : ℕ) (s : ℂ) : ℂ :=
  (C₀ : ℂ) * (A₀ : ℂ) ^ s * (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ r

def sourceThetaReciprocalMellin (C₀ A₀ : ℝ) (r : ℕ) (s : ℂ) : ℂ :=
  (C₀ : ℂ)⁻¹ * Complex.exp (-((Real.log A₀ : ℂ) * s)) * Complex.exp (s ^ 2) *
    ((Complex.Gamma (s + 5 / 6))⁻¹ * (Complex.Gamma (s + 7 / 6))⁻¹) ^ r

theorem sourceThetaReciprocalMellin_entire (C₀ A₀ : ℝ) (r : ℕ) :
    Differentiable ℂ (sourceThetaReciprocalMellin C₀ A₀ r) := by
  have h₁ : Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s + 5 / 6))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add (differentiable_const _))
  have h₂ : Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s + 7 / 6))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add (differentiable_const _))
  have h₃ : Differentiable ℂ (fun s : ℂ => (C₀ : ℂ)⁻¹ * Complex.exp (-((Real.log A₀ : ℂ) * s)) *
      Complex.exp (s ^ 2)) := by fun_prop
  exact h₃.mul ((h₁.mul h₂).pow r)

/-- The reciprocal multiplier cancels the literal Gamma-product symbol
throughout the Mellin half-plane. -/
theorem sourceThetaReciprocalMellin_mul_symbol {C₀ A₀ : ℝ} (hC₀ : 0 < C₀) (hA₀ : 0 < A₀)
    (r : ℕ) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    sourceThetaReciprocalMellin C₀ A₀ r s * sourceThetaMellinSymbol C₀ A₀ r s = Complex.exp (s ^ 2) := by
  have hG₅ := Complex.Gamma_ne_zero_of_re_pos (s := s + 5 / 6) (by
    norm_num [Complex.add_re, Complex.div_ofNat_re]
    linarith)
  have hG₇ := Complex.Gamma_ne_zero_of_re_pos (s := s + 7 / 6) (by
    norm_num [Complex.add_re, Complex.div_ofNat_re]
    linarith)
  have hG : ((Complex.Gamma (s + 5 / 6))⁻¹ * (Complex.Gamma (s + 7 / 6))⁻¹) ^ r *
      (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ r = 1 := by
    have he : (Complex.Gamma (s + 5 / 6))⁻¹ * (Complex.Gamma (s + 7 / 6))⁻¹ *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) = 1 := by
      calc
        _ = ((Complex.Gamma (s + 5 / 6))⁻¹ * Complex.Gamma (s + 5 / 6)) *
            ((Complex.Gamma (s + 7 / 6))⁻¹ * Complex.Gamma (s + 7 / 6)) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hG₅, inv_mul_cancel₀ hG₇, one_mul]
    rw [← mul_pow, he, one_pow]
  let w := (Real.log A₀ : ℂ) * s
  have hA : (A₀ : ℂ) ^ s = Complex.exp w := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hA₀.ne'), ← Complex.ofReal_log hA₀.le]
  have hE : Complex.exp (-w) * Complex.exp w = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  unfold sourceThetaReciprocalMellin sourceThetaMellinSymbol
  rw [hA]
  calc
    _ = ((C₀ : ℂ)⁻¹ * C₀) * (Complex.exp (-w) * Complex.exp w) *
        (((Complex.Gamma (s + 5 / 6))⁻¹ * (Complex.Gamma (s + 7 / 6))⁻¹) ^ r *
          (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ r) * Complex.exp (s ^ 2) := by
      dsimp only [w]
      ring
    _ = _ := by
      rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hC₀.ne'), hE, hG, one_mul, one_mul, one_mul]

private theorem thetaInverseGammaPair_strip (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(Complex.Gamma (s + 5 / 6))⁻¹ * (Complex.Gamma (s + 7 / 6))⁻¹‖ ≤
        C * Real.exp (2 * Real.pi * |s.im|) := by
  obtain ⟨D₅, hD₅, h₅⟩ := reciprocalGamma_strip_exponential_bound (a + 5 / 6) (b + 5 / 6)
  obtain ⟨D₇, hD₇, h₇⟩ := reciprocalGamma_strip_exponential_bound (a + 7 / 6) (b + 7 / 6)
  refine ⟨D₅ * D₇, mul_pos hD₅ hD₇, fun s hs => ?_⟩
  have h₅' := h₅ (s + 5 / 6) (by
    norm_num [Complex.add_re, Complex.div_ofNat_re]
    exact hs)
  have h₇' := h₇ (s + 7 / 6) (by
    norm_num [Complex.add_re, Complex.div_ofNat_re]
    exact hs)
  norm_num [Complex.add_im, Complex.div_ofNat_im] at h₅' h₇'
  rw [norm_mul, norm_inv, norm_inv]
  calc
    _ ≤ (D₅ * Real.exp (Real.pi * |s.im|)) * (D₇ * Real.exp (Real.pi * |s.im|)) :=
      mul_le_mul h₅' h₇' (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = D₅ * D₇ * Real.exp (2 * Real.pi * |s.im|) := by
      rw [show 2 * Real.pi * |s.im| = Real.pi * |s.im| + Real.pi * |s.im| by ring, Real.exp_add]
      ring

/-- Gaussian strip decay of the exact entire reciprocal-Gamma symbol. -/
theorem sourceThetaReciprocalMellin_strip (C₀ A₀ : ℝ) (r : ℕ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc a b →
      ‖sourceThetaReciprocalMellin C₀ A₀ r s‖ ≤ C * Real.exp (-(s.im ^ 2) / 2) := by
  obtain ⟨D, hD, hγ⟩ := thetaInverseGammaPair_strip a b
  let B := max |a| |b|
  let R := 2 * Real.pi * (r : ℝ)
  let E := Real.exp (B * |Real.log A₀|)
  let C := ‖(C₀ : ℂ)⁻¹‖ * E * D ^ r * Real.exp (B ^ 2 + R ^ 2 / 2)
  refine ⟨C, by dsimp only [C, E]; positivity, fun s hs => ?_⟩
  have hB : |s.re| ≤ B := abs_le.mpr ⟨by
    have ha : -B ≤ a := neg_le.mp ((neg_le_abs a).trans (le_max_left _ _))
    exact ha.trans hs.1, hs.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  have ha : ‖Complex.exp (-((Real.log A₀ : ℂ) * s))‖ ≤ E := by
    rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |-(Real.log A₀ * s.re)| := le_abs_self _
      _ = |s.re| * |Real.log A₀| := by rw [abs_neg, abs_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right hB (abs_nonneg _)
  have hγ' : ‖(Complex.Gamma (s + 5 / 6))⁻¹ * (Complex.Gamma (s + 7 / 6))⁻¹‖ ^ r ≤
      D ^ r * Real.exp (R * |s.im|) := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (hγ s hs) r
    rw [mul_pow, ← Real.exp_nat_mul] at h
    have hh : (r : ℝ) * (2 * Real.pi * |s.im|) = R * |s.im| := by dsimp only [R]; ring
    rwa [hh] at h
  have hGaussian : ‖Complex.exp (s ^ 2)‖ = Real.exp (s.re ^ 2 - s.im ^ 2) := by
    rw [Complex.norm_exp, pow_two s, Complex.mul_re, pow_two s.re, pow_two s.im]
  have hQuad : s.re ^ 2 - s.im ^ 2 + R * |s.im| ≤ B ^ 2 + R ^ 2 / 2 - s.im ^ 2 / 2 := by
    have hr : s.re ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hB)).mpr hB
    nlinarith [sq_nonneg (|s.im| - R), sq_abs s.im]
  unfold sourceThetaReciprocalMellin
  rw [norm_mul, norm_mul, norm_mul, norm_pow, hGaussian]
  calc
    _ ≤ (‖(C₀ : ℂ)⁻¹‖ * E * Real.exp (s.re ^ 2 - s.im ^ 2)) * (D ^ r * Real.exp (R * |s.im|)) := by
      gcongr
    _ = (‖(C₀ : ℂ)⁻¹‖ * E * D ^ r) * Real.exp (s.re ^ 2 - s.im ^ 2 + R * |s.im|) := by
      rw [Real.exp_add]
      ring
    _ ≤ (‖(C₀ : ℂ)⁻¹‖ * E * D ^ r) * Real.exp (B ^ 2 + R ^ 2 / 2 - s.im ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hQuad) (by dsimp only [E]; positivity)
    _ = _ := by
      rw [show B ^ 2 + R ^ 2 / 2 - s.im ^ 2 / 2 = (B ^ 2 + R ^ 2 / 2) + (-(s.im ^ 2) / 2) by ring,
        Real.exp_add]
      dsimp only [C]
      ring

theorem sourceThetaReciprocalMellin_verticalIntegrable (C₀ A₀ : ℝ) (r : ℕ) (σ : ℝ) :
    Complex.VerticalIntegrable (sourceThetaReciprocalMellin C₀ A₀ r) σ := by
  obtain ⟨C, _, hC⟩ := sourceThetaReciprocalMellin_strip C₀ A₀ r σ σ
  have hcont : Continuous (fun y : ℝ => sourceThetaReciprocalMellin C₀ A₀ r ((σ : ℂ) + y * Complex.I)) :=
    (sourceThetaReciprocalMellin_entire C₀ A₀ r).continuous.comp (by fun_prop)
  apply (gaussian_half_exp_integrable.const_mul C).mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  have h := hC ((σ : ℂ) + (t : ℂ) * Complex.I) (by simp)
  simpa using h

end
end ArtinMatthews.SourceReflection
