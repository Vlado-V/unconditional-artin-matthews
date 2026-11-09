module

public import ArtinMatthews.SpectralABLExceptionalJWideContour
public import ArtinMatthews.SpectralWeylJBareNormalization


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Complex
noncomputable section

/-- The literal same-sign ABL transform with the spatial factor from (6.1). -/
def spectralABLExceptionalJTransform (a : ℝ) (A : ℕ) (X : ℝ) : ℂ :=
  ((X : ℂ)/2)*∫ t : ℝ,
    spectralWeylJMultiplier t X*spectralABLExceptionalCorrected a A (t : ℂ) ∂spectralKLSpectralMeasure

theorem spectralABLExceptionalJTransform_eq_order (a : ℝ) {A : ℕ} (hA : 3 ≤ A)
    {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => spectralWeylJMultiplier t X*spectralABLExceptionalCorrected a A (t : ℂ))
      spectralKLSpectralMeasure ∧
    spectralABLExceptionalJTransform a A X = (-(2*I)/(Real.pi : ℂ))*
      (∫ t : ℝ, spectralABLExceptionalJOrderIntegrand a A X (t : ℂ)) := by
  let H := spectralABLExceptionalCorrected a A
  let J := fun (ν : ℂ) (x : ℝ) => Complex.besselJ ν (x : ℂ)
  have heq : (fun t : ℝ => spectralWeylBareOrderIntegrand J H X (t : ℂ)) =
      (fun t : ℝ => spectralABLExceptionalJOrderIntegrand a A X (t : ℂ)) := by
    funext t
    simp only [spectralWeylBareOrderIntegrand,spectralABLExceptionalJOrderIntegrand,
      spectralABLExceptionalWideCorrected_real,H,J]
  obtain ⟨_,_,h0⟩ := spectralABLExceptionalJOrder_line A 0 hA (Nat.zero_le A)
  have hI : Integrable (fun t : ℝ => spectralWeylBareOrderIntegrand J H X (t : ℂ)) := by
    rw [heq]
    simpa only [Nat.cast_zero,zero_mul,add_zero] using (h0 a X hX).1
  have h := spectralWeylJBare_eq_orderIntegral H (spectralABLExceptionalCorrected_even a A) hX hI
  refine ⟨h.1,?_⟩
  unfold spectralABLExceptionalJTransform
  change ((X : ℂ)/2)*(∫ t : ℝ, spectralWeylJMultiplier t X*H (t : ℂ) ∂spectralKLSpectralMeasure) = _
  rw [h.2,heq,← mul_assoc]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr hX.ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

theorem spectralABLExceptionalJTransform_source (a : ℝ) {A : ℕ} (hA : 3 ≤ A)
    {X : ℝ} (hX : 0 < X) :
    spectralABLExceptionalJTransform a A X = ((2*I)/(Real.pi : ℂ))*
      (∫ t : ℝ, (t : ℂ)*spectralABLExceptionalCorrected a A (t : ℂ)*
        Complex.besselJ (2*(t : ℂ)*I) (X : ℂ)) := by
  let F : ℝ → ℂ := fun t => spectralABLExceptionalJOrderIntegrand a A X (t : ℂ)
  have heq : (fun t : ℝ => F (-t)) = fun t : ℝ =>
      -((t : ℂ)*spectralABLExceptionalCorrected a A (t : ℂ)*Complex.besselJ (2*(t : ℂ)*I) (X : ℂ)) := by
    funext t
    simp only [F,spectralABLExceptionalJOrderIntegrand,spectralABLExceptionalWideCorrected_real,
      Complex.ofReal_neg,spectralABLExceptionalCorrected_even]
    rw [show -2*I*(-(t : ℂ)) = 2*(t : ℂ)*I by ring]
    ring
  calc
    _ = (-(2*I)/(Real.pi : ℂ))*(∫ t : ℝ, F t) := (spectralABLExceptionalJTransform_eq_order a hA hX).2
    _ = (-(2*I)/(Real.pi : ℂ))*(∫ t : ℝ, F (-t)) := by
      rw [integral_neg_eq_self F (volume : Measure ℝ)]
    _ = _ := by rw [heq,integral_neg]; ring

theorem spectralABLExceptionalJTransform_eq_shifted (a : ℝ) {A : ℕ} (hA : 3 ≤ A)
    {X : ℝ} (hX : 0 < X) :
    spectralABLExceptionalJTransform a A X = (-(2*I)/(Real.pi : ℂ))*
      (∫ t : ℝ, spectralABLExceptionalJOrderIntegrand a A X ((t : ℂ)+(A : ℂ)*I)) := by
  rw [(spectralABLExceptionalJTransform_eq_order a hA hX).2,spectralABLExceptionalJOrder_shift a hA hX]

theorem spectralABLExceptionalJ_phase_scaling (a X : ℝ) (A : ℕ) (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.exp (4*(A : ℝ)*|Real.log a|)*X^(2*(A : ℝ)) = (X/a^2)^(2*A) := by
  have hphase : Real.exp (4*(A : ℝ)*|Real.log a|) = (a^(4*A))⁻¹ := by
    rw [abs_of_nonpos (Real.log_nonpos ha.le ha1),← Real.rpow_natCast a (4*A),
      Real.rpow_def_of_pos ha,← Real.exp_neg]
    congr 1
    push_cast
    ring
  have hpower : X^(2*(A : ℝ)) = X^(2*A) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using Real.rpow_natCast X (2*A)
  rw [hphase,hpower,div_pow,← pow_mul,show 2*(2*A) = 4*A by omega]
  ring

theorem spectralABLExceptionalJTransform_allX (A : ℕ) (hA : 3 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ a X : ℝ, 0 < a → a ≤ 1 → 0 < X →
      ‖spectralABLExceptionalJTransform a A X‖ ≤ C*min 1 ((X/a^2)^(2*A)) := by
  obtain ⟨D0,hD0,h0⟩ := spectralABLExceptionalJOrder_line A 0 hA (Nat.zero_le A)
  obtain ⟨D1,hD1,h1⟩ := spectralABLExceptionalJOrder_line A A hA le_rfl
  let C := (2/Real.pi)*(D0+D1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro a X ha ha1 hX
  have hs : ‖-(2*I)/(Real.pi : ℂ)‖ = (2 : ℝ)/Real.pi := by
    rw [norm_div,norm_neg,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  have hreal : ‖∫ t : ℝ, spectralABLExceptionalJOrderIntegrand a A X (t : ℂ)‖ ≤ D0 := by
    simpa only [Nat.cast_zero,zero_mul,mul_zero,add_zero,Real.exp_zero,Real.rpow_zero,mul_one] using (h0 a X hX).2
  have htop : ‖∫ t : ℝ, spectralABLExceptionalJOrderIntegrand a A X ((t : ℂ)+(A : ℂ)*I)‖ ≤
      D1*((X/a^2)^(2*A)) := by
    have h := (h1 a X hX).2
    rwa [mul_assoc,spectralABLExceptionalJ_phase_scaling a X A ha ha1] at h
  rw [mul_min_of_nonneg _ _ hC.le]
  apply le_min
  · rw [(spectralABLExceptionalJTransform_eq_order a hA hX).2,norm_mul,hs,mul_one]
    exact mul_le_mul_of_nonneg_left (hreal.trans (by linarith)) (by positivity)
  · rw [spectralABLExceptionalJTransform_eq_shifted a hA hX,norm_mul,hs]
    calc
      _ ≤ (2/Real.pi)*(D1*((X/a^2)^(2*A))) := mul_le_mul_of_nonneg_left htop (by positivity)
      _ = ((2/Real.pi)*D1)*((X/a^2)^(2*A)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by positivity)

end
end ArtinMatthews
