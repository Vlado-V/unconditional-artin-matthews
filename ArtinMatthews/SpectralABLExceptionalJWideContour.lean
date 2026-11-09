module

public import ArtinMatthews.SpectralABLExceptionalJOrder
public import ArtinMatthews.SpectralWeylWideGaussianContour


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Complex
noncomputable section

theorem spectralABLExceptionalJOrder_strip_bound (a : ℝ) {A : ℕ} (hA : 1 ≤ A)
    {X : ℝ} (hX : 0 < X) :
    ∃ C : ℝ, 0 < C ∧ ∀ t y : ℝ, 0 ≤ y → y ≤ (A : ℝ) →
      ‖spectralABLExceptionalJOrderIntegrand a A X ((t : ℂ)+(y : ℂ)*I)‖ ≤
        C*(1+t^2)*Real.exp (Real.pi*|t|) := by
  obtain ⟨H,hH,hHbound⟩ := spectralABLExceptionalWideCorrected_strip_bound a hA
  obtain ⟨J,hJ,hJbound⟩ := spectral_besselJ_closed_strip_allX (2*(A : ℝ)) (by positivity)
  let P : ℝ := 1+X^(2*(A : ℝ))
  refine ⟨2*((A : ℝ)+1)*H*J*P,by dsimp [P];positivity,?_⟩
  intro t y hy0 hyA
  let z : ℂ := (t : ℂ)+(y : ℂ)*I
  have hz : ‖z‖ ≤ ((A : ℝ)+1)*(1+|t|) := by
    apply (spectralWeylOrder_horizontal_norm_le t y hy0).trans
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) A) (abs_nonneg t)]
  have hpow : X^(2*y) ≤ P := by
    by_cases hX1 : X ≤ 1
    · exact (Real.rpow_le_one hX.le hX1 (by linarith)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hX.le _))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hX1) (by linarith : 2*y ≤ 2*(A : ℝ))).trans
        (le_add_of_nonneg_left zero_le_one)
  have hj0 := hJbound (2*y) (-t) X (by linarith) (by linarith) hX
  have hj : ‖Complex.besselJ (-2*I*z) (X : ℂ)‖ ≤ J*(1+|t|)*Real.exp (Real.pi*|t|)*P := by
    rw [show -2*I*z = ((2*y : ℝ) : ℂ)+2*((-t : ℝ) : ℂ)*I from spectralWeylOrder_horizontal t y]
    rw [abs_neg] at hj0
    exact hj0.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hh : ‖spectralABLExceptionalWideCorrected a A z‖ ≤ H :=
    hHbound t y (by simpa only [abs_of_nonneg hy0] using hyA)
  have ht : (1+|t|)^2 ≤ 2*(1+t^2) := by
    nlinarith [sq_abs t,sq_nonneg (|t|-1)]
  change ‖z*spectralABLExceptionalWideCorrected a A z*Complex.besselJ (-2*I*z) (X : ℂ)‖ ≤ _
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (((A : ℝ)+1)*(1+|t|))*H*(J*(1+|t|)*Real.exp (Real.pi*|t|)*P) := by gcongr
    _ = (((A : ℝ)+1)*H*J*P)*((1+|t|)^2*Real.exp (Real.pi*|t|)) := by ring
    _ ≤ (((A : ℝ)+1)*H*J*P)*(2*(1+t^2)*Real.exp (Real.pi*|t|)) := by gcongr
    _ = _ := by ring

theorem spectralABLExceptionalJOrder_shift (a : ℝ) {A : ℕ} (hA : 3 ≤ A)
    {X : ℝ} (hX : 0 < X) :
    (∫ t : ℝ, spectralABLExceptionalJOrderIntegrand a A X (t : ℂ)) =
      ∫ t : ℝ, spectralABLExceptionalJOrderIntegrand a A X ((t : ℂ)+(A : ℂ)*I) := by
  obtain ⟨C,hC,hbound⟩ := spectralABLExceptionalJOrder_strip_bound a (by omega : 1 ≤ A) hX
  obtain ⟨_,_,h0⟩ := spectralABLExceptionalJOrder_line A 0 hA (Nat.zero_le A)
  obtain ⟨_,_,hTop⟩ := spectralABLExceptionalJOrder_line A A hA le_rfl
  have hZero : Integrable (fun t : ℝ => spectralABLExceptionalJOrderIntegrand a A X (t : ℂ)) := by
    simpa only [Nat.cast_zero,zero_mul,add_zero] using (h0 a X hX).1
  have hEnd : Integrable (fun t : ℝ =>
      spectralABLExceptionalJOrderIntegrand a A X ((t : ℂ)+((A : ℝ) : ℂ)*I)) := by
    simpa only [Complex.ofReal_natCast] using (hTop a X hX).1
  have hshift := spectral_horizontal_integral_eq_of_gaussian_envelope
    (spectralABLExceptionalJOrderIntegrand a A X) (Nat.cast_nonneg A) hC.le
    (fun _z hz0 hzA => spectralABLExceptionalJOrder_differentiableAt a (by omega : 1 ≤ A) hX hz0 hzA)
    hbound hZero hEnd
  simpa only [Complex.ofReal_natCast] using hshift

end
end ArtinMatthews
