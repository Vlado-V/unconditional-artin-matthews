module

public import ArtinMatthews.ShiftedABLMellinModuli
public import ArtinMatthews.MarkedMajorOscillatoryDerivatives
public import ArtinMatthews.ShiftedABLSourceBudget
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! Actual modulus-profile derivatives with exact reciprocal scale and
polynomial dependence on both unrestricted Mellin heights. -/

noncomputable section
open Complex Set Filter MeasureTheory OAI
open scoped ContDiff BigOperators Topology

namespace ArtinMatthews

private def shiftedABLPositiveCoordinate (x : ℝ) : ℝ :=
  1+(shiftedSourcePlateau x).re*(x-1)

private theorem shiftedABLPositiveCoordinate_smooth :
    ContDiff ℝ ∞ shiftedABLPositiveCoordinate :=
  contDiff_const.add ((Complex.reCLM.contDiff.comp shiftedSourcePlateau_smooth).mul
    (contDiff_id.sub contDiff_const))

private theorem shiftedABLPositiveCoordinate_pos (x : ℝ) : 0 < shiftedABLPositiveCoordinate x := by
  have h0 : 0 ≤ (shiftedSourcePlateau x).re := by
    unfold shiftedSourcePlateau
    rw [Complex.ofReal_re]
    apply ContDiffBump.nonneg
  have h1 : (shiftedSourcePlateau x).re ≤ 1 :=
    (Complex.re_le_norm _).trans (shiftedSourcePlateau_norm _)
  by_cases hx : shiftedSourcePlateau x = 0
  · simp [shiftedABLPositiveCoordinate,hx]
  have hx' := (shiftedSourcePlateau_support hx).1
  have hmul := mul_le_mul_of_nonneg_left (show -(1/2 : ℝ) ≤ x-1 by linarith) h0
  dsimp [shiftedABLPositiveCoordinate]
  linarith

private theorem shiftedABLPositiveCoordinate_eq {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    shiftedABLPositiveCoordinate x = x := by
  simp only [shiftedABLPositiveCoordinate,shiftedSourcePlateau_one _ hx,
    Complex.one_re,one_mul]
  ring

private def shiftedABLProfileAmplitude (x : ℝ) : ℂ :=
  (circleSmoothCutoff (3*x)/shiftedABLPositiveCoordinate x : ℝ)

private def shiftedABLProfilePhase (x : ℝ) : ℝ :=
  -4*Real.pi*Real.log (shiftedABLPositiveCoordinate x)

private theorem shiftedABLProfileAmplitude_smooth : ContDiff ℝ ∞ shiftedABLProfileAmplitude :=
  Complex.ofRealCLM.contDiff.comp
    ((circleSmoothCutoff_contDiff.comp (contDiff_const.mul contDiff_id)).div
      shiftedABLPositiveCoordinate_smooth (fun x => (shiftedABLPositiveCoordinate_pos x).ne'))

private theorem shiftedABLProfilePhase_smooth : ContDiff ℝ ∞ shiftedABLProfilePhase :=
  contDiff_const.mul (shiftedABLPositiveCoordinate_smooth.log
    (fun x => (shiftedABLPositiveCoordinate_pos x).ne'))

private theorem shiftedABLProfile_support (t : ℝ) :
    Function.support (markedOscillatoryFamily shiftedABLProfileAmplitude shiftedABLProfilePhase t)
      ⊆ Icc (1 : ℝ) 2 := by
  intro x hx
  have h : 3*x ∈ Function.support circleSmoothCutoff := by
    intro hn
    apply hx
    simp [markedOscillatoryFamily,shiftedABLProfileAmplitude,hn]
  rw [circleSmoothCutoff_support] at h
  exact ⟨by linarith [h.1],by linarith [h.2]⟩

private theorem shiftedABLMellinModulusWeight_normalized {F L : ℕ}
    (hF : 0 < F) (hL : 0 < L) (z : ℝ × ℝ) :
    shiftedABLMellinModulusWeight F L z =
      fun c => markedOscillatoryFamily shiftedABLProfileAmplitude shiftedABLProfilePhase
        (z.1+z.2) ((3*(L : ℝ)/(F : ℝ))⁻¹*c) := by
  funext c
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  let x := (3*(L : ℝ)/(F : ℝ))⁻¹*c
  have hx : (F : ℝ)*c/(3*(L : ℝ)) = x := by
    dsimp [x]
    rw [inv_div]
    ring
  have h3 : (F : ℝ)*c/(L : ℝ) = 3*x := by
    rw [← hx]
    field_simp [hL0] <;> ring
  have hinv : 3*(L : ℝ)/((F : ℝ)*c) = x⁻¹ := by rw [← hx, inv_div]
  unfold shiftedABLMellinModulusWeight shiftedABLMellinCirclePhase circleSmoothScaled
  change (circleSmoothCutoff ((F : ℝ)*c/(L : ℝ)) : ℂ) *
    ((3*(L : ℝ)/((F : ℝ)*c) : ℝ) : ℂ) *
    FourierBridge.logPhase z.1 (-2*Real.log ((F : ℝ)*c/(3*(L : ℝ)))) *
    FourierBridge.logPhase z.2 (-2*Real.log ((F : ℝ)*c/(3*(L : ℝ)))) =
      markedOscillatoryFamily shiftedABLProfileAmplitude shiftedABLProfilePhase (z.1+z.2) x
  rw [h3,hinv,hx]
  by_cases hzero : circleSmoothCutoff (3*x) = 0
  · simp [hzero,markedOscillatoryFamily,shiftedABLProfileAmplitude]
  have hs : 3*x ∈ Ioo (3 : ℝ) 6 := by rw [← circleSmoothCutoff_support]; exact hzero
  have hp := shiftedABLPositiveCoordinate_eq (show x ∈ Icc (1 : ℝ) 2 from
    ⟨by linarith [hs.1],by linarith [hs.2]⟩)
  unfold markedOscillatoryFamily shiftedABLProfileAmplitude markedOscillatoryPhase
    shiftedABLProfilePhase markedRealOscillator FourierBridge.logPhase
  rw [hp,div_eq_mul_inv,Complex.ofReal_mul]
  have he : Complex.exp (((2*Real.pi*z.1*(-2*Real.log x) : ℝ) : ℂ)*Complex.I) *
      Complex.exp (((2*Real.pi*z.2*(-2*Real.log x) : ℝ) : ℂ)*Complex.I) =
      Complex.exp (Complex.I*((((z.1+z.2)*(-4*Real.pi*Real.log x)) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  convert congrArg (fun v : ℂ => (circleSmoothCutoff (3*x) : ℂ)*(x⁻¹ : ℂ)*v) he using 1 <;> push_cast <;> ring


theorem shiftedABLMellinModulusWeight_contDiff {F L : ℕ}
    (hF : 0 < F) (hL : 0 < L) (z : ℝ × ℝ) :
    ContDiff ℝ ∞ (shiftedABLMellinModulusWeight F L z) := by
  rw [shiftedABLMellinModulusWeight_normalized hF hL]
  exact (markedOscillatoryFamily_contDiff _ _ shiftedABLProfileAmplitude_smooth
    shiftedABLProfilePhase_smooth _).comp (contDiff_const.mul contDiff_id)

/-- The literal (Q/q) profile has the required reciprocal modulus
scale at every derivative order. The heights remain unbounded. -/
theorem shiftedABLMellinModulusWeight_derivative_bound (j : ℕ) :
    ∃ Cj : ℝ, 0 < Cj ∧ ∀ (F L : ℕ), 0 < F → 0 < L → ∀ (z : ℝ × ℝ) (c : ℝ),
      ‖iteratedDeriv j (shiftedABLMellinModulusWeight F L z) c‖ ≤
        Cj*(1+|z.1|+|z.2|)^j/(3*(L : ℝ)/(F : ℝ))^j := by
  obtain ⟨Cj,hCj,hbound⟩ := markedOscillatoryFamily_compact_derivative_bound
    shiftedABLProfileAmplitude shiftedABLProfilePhase shiftedABLProfileAmplitude_smooth
    shiftedABLProfilePhase_smooth (Icc (1 : ℝ) 2) isCompact_Icc j
  refine ⟨Cj,hCj,?_⟩
  intro F L hF hL z c
  let scale : ℝ := 3*(L : ℝ)/(F : ℝ)
  let profile := markedOscillatoryFamily shiftedABLProfileAmplitude shiftedABLProfilePhase (z.1+z.2)
  let x := scale⁻¹*c
  have hscale : 0 < scale := by
    have hF0 : (0 : ℝ) < F := by exact_mod_cast hF
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
    dsimp [scale]
    positivity
  have hp : ContDiff ℝ ∞ profile := markedOscillatoryFamily_contDiff _ _
    shiftedABLProfileAmplitude_smooth shiftedABLProfilePhase_smooth _
  have hder : ‖iteratedDeriv j profile x‖ ≤ Cj*(1+|z.1|+|z.2|)^j := by
    by_cases hx : x ∈ Icc (1 : ℝ) 2
    · have hh := hbound (z.1+z.2) x hx
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
      apply hh.trans
      have ht : 1+|z.1+z.2| ≤ 1+|z.1|+|z.2| := by linarith [abs_add_le z.1 z.2]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht j) hCj.le
    · have hsupport : tsupport profile ⊆ Icc (1 : ℝ) 2 :=
        closure_minimal (shiftedABLProfile_support (z.1+z.2)) isClosed_Icc
      have hzero : profile =ᶠ[𝓝 x] fun _ => 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun hn => hx (hsupport hn))
      rw [hzero.iteratedDeriv_eq j]
      simp <;> positivity
  rw [shiftedABLMellinModulusWeight_normalized hF hL]
  change ‖iteratedDeriv j (fun t => profile (scale⁻¹*t)) c‖ ≤
    Cj*(1+|z.1|+|z.2|)^j/scale^j
  rw [iteratedDeriv_comp_const_smul (hp.of_le (by simp)), norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hscale.le) j)]
  change scale⁻¹^j*‖iteratedDeriv j profile x‖ ≤ _
  calc
    _ ≤ scale⁻¹^j*(Cj*(1+|z.1|+|z.2|)^j) :=
      mul_le_mul_of_nonneg_left hder (by positivity)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring


/-- A polynomial height factor multiplies the literal spectral
conductor by the same factor. -/
theorem shiftedABLMellin_spectralParameter_height (C R Z W : ℝ) (n r s : ℕ) :
    ablTheorem24SpectralParameter C R (Z*W) n r s =
      ablTheorem24SpectralParameter C R Z n r s * W := by
  unfold ablTheorem24SpectralParameter
  ring

/-- The square-root cutoff loss uses at most one height factor when
the spectral exponent is at most one. -/
theorem shiftedABLMellin_principal_loss_height {Z P' W δ : ℝ}
    (hZ : 0 ≤ Z) (hP : 0 ≤ P') (hW : 1 ≤ W) (hδ : δ ≤ 1) :
    Real.sqrt ((Z*W)*(P'*W)^δ) ≤ Real.sqrt (Z*(P')^δ)*W := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  rw [Real.mul_rpow hP hW0,show Z*W*((P')^δ*W^δ) = (Z*(P')^δ)*(W*W^δ) by ring,
    Real.sqrt_mul (mul_nonneg hZ (Real.rpow_nonneg hP _))]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_iff.2
  refine ⟨hW0, ?_⟩
  have hp : W^δ ≤ W := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hW hδ
  simpa only [pow_two] using mul_le_mul_of_nonneg_left hp hW0


/-- The actual Schwartz kernels absorb every fixed polynomial loss in
the two unrestricted Mellin heights. -/
theorem shiftedABLMellin_product_moment_bound (b1 b2 : SchwartzMap ℝ ℂ) (J : ℕ) :
    let f (z : ℝ × ℝ) := (1+|z.1|+|z.2|)^J*(‖b1 z.1‖*‖b2 z.2‖)
    Integrable f ∧ (∫ z : ℝ × ℝ, f z) ≤
      (∫ t : ℝ, (1+‖t‖)^J*‖b1 t‖)*(∫ t : ℝ, (1+‖t‖)^J*‖b2 t‖) := by
  intro f
  let g1 (t : ℝ) := (1+‖t‖)^J*‖b1 t‖
  let g2 (t : ℝ) := (1+‖t‖)^J*‖b2 t‖
  have hg : Integrable (fun z : ℝ × ℝ => g1 z.1*g2 z.2) := by
    rw [Measure.volume_eq_prod]
    exact (shifted_log_coefficient_moment_integrable b1 J).mul_prod
      (shifted_log_coefficient_moment_integrable b2 J)
  have hnonneg (z : ℝ × ℝ) : 0 ≤ f z := by dsimp [f]; positivity
  have hle (z : ℝ × ℝ) : f z ≤ g1 z.1*g2 z.2 := by
    have h : 1+|z.1|+|z.2| ≤ (1+|z.1|)*(1+|z.2|) := by
      nlinarith [mul_nonneg (abs_nonneg z.1) (abs_nonneg z.2)]
    calc
      _ ≤ ((1+|z.1|)*(1+|z.2|))^J*(‖b1 z.1‖*‖b2 z.2‖) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h J) (by positivity)
      _ = _ := by dsimp [g1,g2]; simp only [mul_pow,Real.norm_eq_abs]; ring
  have hf : Integrable f := hg.mono'
    (by apply Continuous.aestronglyMeasurable; dsimp [f]; fun_prop)
    (Eventually.of_forall (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hnonneg z)]; exact hle z))
  refine ⟨hf,(integral_mono hf hg hle).trans_eq ?_⟩
  rw [Measure.volume_eq_prod,integral_prod_mul]

end ArtinMatthews
