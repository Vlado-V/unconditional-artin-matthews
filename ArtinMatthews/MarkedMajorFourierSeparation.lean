module

public import ArtinMatthews.MarkedMajorFourierSeparationInversion
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Mellin separation, including the genuine first-coordinate
Jacobian `1/X` and absolute integrability of the separated kernel. -/
namespace ArtinMatthews
open MeasureTheory Complex
open scoped FourierTransform SchwartzMap
noncomputable section

def markedMajorMellinFrequencyScale (X : ℝ) (hX : X ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (LinearEquiv.prodCongr (LinearEquiv.smulOfNeZero ℝ ℝ X⁻¹ (inv_ne_zero hX))
    (LinearEquiv.refl ℝ ℝ)).toContinuousLinearEquiv

theorem markedMajorMellinFrequencyScale_apply (X : ℝ) (hX : X ≠ 0) (p : ℝ × ℝ) :
    markedMajorMellinFrequencyScale X hX p = (p.1/X,p.2) := by
  change (X⁻¹*p.1,p.2) = _
  simp only [div_eq_mul_inv,mul_comm]

def markedMajorScaledFourierCoefficient (g : SchwartzMap (ℝ × ℝ) ℂ)
    (X : ℝ) (hX : X ≠ 0) : SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (markedMajorMellinFrequencyScale X hX)
    (markedMajorFourierCoefficient g)

theorem markedMajorScaledFourierCoefficient_apply (g : SchwartzMap (ℝ × ℝ) ℂ)
    (X : ℝ) (hX : X ≠ 0) (p : ℝ × ℝ) :
    markedMajorScaledFourierCoefficient g X hX p = markedMajorFourierCoefficient g (p.1/X,p.2) := by
  change markedMajorFourierCoefficient g (markedMajorMellinFrequencyScale X hX p) = _
  rw [markedMajorMellinFrequencyScale_apply]

theorem markedMajorFourier_scaled_phase_integrable (g : SchwartzMap (ℝ × ℝ) ℂ)
    {X : ℝ} (hX : X ≠ 0) (x : ℝ × ℝ) :
    Integrable (fun p : ℝ × ℝ => markedMajorFourierCoefficient g (p.1/X,p.2) *
      markedMajorFourierPhase (p.1/X,p.2) x) := by
  have hg : Integrable (fun p : ℝ × ℝ => markedMajorFourierCoefficient g (p.1/X,p.2)) := by
    convert ((markedMajorScaledFourierCoefficient g X hX).integrable (μ := volume)) using 1
    funext p
    exact (markedMajorScaledFourierCoefficient_apply g X hX p).symm
  apply hg.mul_bdd (c := 1)
  · apply Continuous.aestronglyMeasurable
    unfold markedMajorFourierPhase
    fun_prop
  · exact Filter.Eventually.of_forall (fun p => le_of_eq (markedMajorFourierPhase_norm (p.1/X,p.2) x))

theorem markedMajorFourier_inversion_scaled (g : SchwartzMap (ℝ × ℝ) ℂ)
    {X : ℝ} (hX : 0 < X) (ζ z : ℝ) :
    g (ζ,z) = (X : ℂ)⁻¹ * ∫ t : ℝ, ∫ s : ℝ,
      markedMajorFourierCoefficient g (t/X,s) *
        Complex.exp ((((t/X)*ζ+s*z : ℝ) : ℂ)*I) := by
  let H : ℝ → ℂ := fun v => ∫ s : ℝ,
    markedMajorFourierCoefficient g (v,s)*Complex.exp (((v*ζ+s*z : ℝ) : ℂ)*I)
  have hi : g (ζ,z) = ∫ v, H v := markedMajorFourier_inversion_iterated g ζ z
  have hc := Measure.integral_comp_div H X
  rw [abs_of_pos hX] at hc
  change g (ζ,z) = (X : ℂ)⁻¹ * ∫ t, H (t/X)
  rw [hc,Complex.real_smul,← mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hX.ne'),one_mul]
  exact hi

theorem markedMajor_mellin_phase {X w w' : ℝ} (hX : X ≠ 0) (hw : 0 < w) (hw' : 0 < w')
    (t s : ℝ) :
    markedMajorFourierPhase (t/X,s) (X*(Real.log w-Real.log w'),Real.log w') =
      (w : ℂ)^((t : ℂ)*I) * (w' : ℂ)^(((s-t : ℝ) : ℂ)*I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hw.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hw'.ne'),
    ← Complex.ofReal_log hw.le,← Complex.ofReal_log hw'.le,← Complex.exp_add]
  unfold markedMajorFourierPhase
  congr 1
  have he : (t/X)*(X*(Real.log w-Real.log w'))+s*Real.log w' =
      Real.log w*t + Real.log w'*(s-t) := by field_simp; ring
  change (((t/X*(X*(Real.log w-Real.log w'))+s*Real.log w' : ℝ) : ℂ)*I) = _
  rw [he]
  push_cast
  ring

theorem markedMajor_mellin_separation (g : SchwartzMap (ℝ × ℝ) ℂ)
    {X w w' : ℝ} (hX : 0 < X) (hw : 0 < w) (hw' : 0 < w') :
    g (X*(Real.log w-Real.log w'),Real.log w') =
      (X : ℂ)⁻¹ * ∫ t : ℝ, ∫ s : ℝ,
        markedMajorFourierCoefficient g (t/X,s) *
          ((w : ℂ)^((t : ℂ)*I) * (w' : ℂ)^(((s-t : ℝ) : ℂ)*I)) := by
  rw [markedMajorFourier_inversion_scaled g hX]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  apply integral_congr_ae
  filter_upwards with s
  rw [← markedMajor_mellin_phase hX.ne' hw hw']
  rfl

theorem markedMajor_mellin_separated_integrable (g : SchwartzMap (ℝ × ℝ) ℂ)
    {X w w' : ℝ} (hX : 0 < X) (hw : 0 < w) (hw' : 0 < w') :
    Integrable (fun p : ℝ × ℝ => markedMajorFourierCoefficient g (p.1/X,p.2) *
      ((w : ℂ)^((p.1 : ℂ)*I) * (w' : ℂ)^(((p.2-p.1 : ℝ) : ℂ)*I))) := by
  convert markedMajorFourier_scaled_phase_integrable g hX.ne'
    (X*(Real.log w-Real.log w'),Real.log w') using 1
  funext p
  rw [markedMajor_mellin_phase hX.ne' hw hw']

end
end ArtinMatthews
