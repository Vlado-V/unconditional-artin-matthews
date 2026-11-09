module

public import ArtinMatthews.QuadraticHeckeDualProfile
public import Mathlib.Analysis.MellinInversion


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Complex SourcePhysical
open scoped ContDiff FourierTransform
noncomputable section

theorem quadraticHeckeDualProfileAt_eq_mellinInv (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (σ x : ℝ) :
    quadraticHeckeDualProfileAt A r w σ x = mellinInv σ (quadraticHeckeDualMellin A r w) x := by
  simp only [quadraticHeckeDualProfileAt, quadraticHeckeDualIntegrand, mellinInv,
    smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat]

theorem quadraticHeckeDualMellin_verticalIntegrable (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ : ℝ} (hσ : 1 / 4 ≤ σ) :
    Integrable (fun t : ℝ => quadraticHeckeDualMellin A r w ((σ : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨B, hB⟩ := exists_nat_gt σ
  obtain ⟨C, _, hdecay⟩ := quadraticHeckeDualMellin_strip_decay A r B w hcompact hpositive hsmooth 2
  have hCont : Continuous (fun t : ℝ => quadraticHeckeDualMellin A r w ((σ : ℂ) + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ht : ContinuousAt (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) t := by fun_prop
    exact (quadraticHeckeDualMellin_differentiableAt A r w hcompact hpositive hsmooth.continuous
      ((σ : ℂ) + (t : ℂ) * I) (by simp; linarith)).continuousAt.comp' (f := _) (x := t) ht
  refine (sourceContourHeightWeight_integrable.const_mul C).mono' hCont.aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  have h := hdecay ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσ) (by simp; linarith)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, I_im,
    I_re, mul_one, mul_zero, add_zero, zero_add] at h
  have h' := sourceContourHeightWeight_of_rapid 0 t C _ (norm_nonneg _) h
  simpa only [pow_zero, one_mul] using h'

private theorem quadraticHeckeDualProfile_logIntegrable (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ : ℝ} (hσ : 1 / 4 < σ)
    (hmeas : AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-σ * u) • quadraticHeckeDualProfile A r w (Real.exp (-u)))) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • quadraticHeckeDualProfile A r w (Real.exp (-u))) := by
  obtain ⟨C₀, hC₀, hsmall⟩ := quadraticHeckeDualProfile_power_bound A r w
    hcompact hpositive hsmooth (σ := 1 / 4) le_rfl
  obtain ⟨Cbig, hCbig, hlarge⟩ := quadraticHeckeDualProfile_power_bound A r w
    hcompact hpositive hsmooth (σ := σ + 1) (by linarith)
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · refine ((integrableOn_exp_mul_Iic (a := 1) (by norm_num) 0).const_mul Cbig).mono'
      (hmeas.mono_measure Measure.restrict_le_self) (ae_restrict_of_forall_mem measurableSet_Iic fun u _ => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ Real.exp (-σ * u) * (Cbig * Real.exp (-u) ^ (-(σ + 1))) :=
        mul_le_mul_of_nonneg_left (hlarge _ (Real.exp_pos _)) (Real.exp_nonneg _)
      _ = Cbig * Real.exp (1 * u) := by
        rw [← Real.exp_mul, mul_left_comm, ← Real.exp_add]
        congr 2
        ring
  · refine ((integrableOn_exp_mul_Ioi (a := 1 / 4 - σ) (by linarith) 0).const_mul C₀).mono'
      (hmeas.mono_measure Measure.restrict_le_self) (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ Real.exp (-σ * u) * (C₀ * Real.exp (-u) ^ (-(1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hsmall _ (Real.exp_pos _)) (Real.exp_nonneg _)
      _ = C₀ * Real.exp ((1 / 4 - σ) * u) := by
        rw [← Real.exp_mul, mul_left_comm, ← Real.exp_add]
        congr 2
        ring

/-- The inverse contour transform has exactly the original dual Mellin symbol. -/
theorem quadraticHeckeDualProfile_mellin (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) (s : ℂ) (hs : 1 / 4 < s.re) :
    mellin (quadraticHeckeDualProfile A r w) s = quadraticHeckeDualMellin A r w s := by
  let σ := s.re
  let g (t : ℝ) := quadraticHeckeDualMellin A r w ((σ : ℂ) + 2 * Real.pi * (t : ℂ) * I)
  have hgi : Integrable g := by
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have h := Integrable.comp_mul_left'
      (quadraticHeckeDualMellin_verticalIntegrable A r w hcompact hpositive hsmooth hs.le) hπ
    simpa only [g, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_assoc] using h
  have hgc : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ht : ContinuousAt (fun u : ℝ => (σ : ℂ) + 2 * Real.pi * (u : ℂ) * I) t := by fun_prop
    exact (quadraticHeckeDualMellin_differentiableAt A r w hcompact hpositive hsmooth.continuous
      ((σ : ℂ) + 2 * Real.pi * (t : ℂ) * I) (by simp [Complex.mul_re, σ]; linarith)).continuousAt.comp' (f := _) (x := t) ht
  have hlog (u : ℝ) :
      Real.exp (-σ * u) • quadraticHeckeDualProfile A r w (Real.exp (-u)) = 𝓕⁻ g u := by
    have hx : 0 < Real.exp (-u) := Real.exp_pos _
    have he : quadraticHeckeDualProfile A r w (Real.exp (-u)) =
        quadraticHeckeDualProfileAt A r w σ (Real.exp (-u)) := by
      unfold quadraticHeckeDualProfile
      rcases le_total (1 / 2 : ℝ) σ with h | h
      · exact quadraticHeckeDualProfileAt_eq A r w hcompact hpositive hsmooth (by norm_num) h hx
      · exact (quadraticHeckeDualProfileAt_eq A r w hcompact hpositive hsmooth hs.le h hx).symm
    rw [he, quadraticHeckeDualProfileAt_eq_mellinInv, mellinInv_eq_fourierInv _ _ hx,
      Real.log_exp, neg_neg]
    change (Real.exp (-σ * u) : ℂ) * (((Real.exp (-u) : ℝ) : ℂ) ^ (-σ : ℂ) * 𝓕⁻ g u) = _
    have hp : ((Real.exp (-u) : ℝ) : ℂ) ^ (-σ : ℂ) = ((Real.exp (-u) ^ (-σ : ℝ) : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_neg] using (Complex.ofReal_cpow hx.le (-σ)).symm
    rw [hp, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_mul, ← Real.exp_add]
    have h : -σ * u + -u * -σ = 0 := by ring
    rw [h, Real.exp_zero, Complex.ofReal_one, one_mul]
  have hInvCont : Continuous (𝓕⁻ g) := by
    have hg' : Continuous (𝓕 g) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hgi
    exact (hg'.comp continuous_neg).congr (fun u => (Real.fourierInv_eq_fourier_neg g u).symm)
  have hlogeq : (fun u : ℝ => Real.exp (-σ * u) •
      quadraticHeckeDualProfile A r w (Real.exp (-u))) = 𝓕⁻ g := funext hlog
  have hlogi : Integrable (𝓕⁻ g) :=
    hlogeq ▸ quadraticHeckeDualProfile_logIntegrable A r w hcompact hpositive hsmooth hs
      (hlogeq.symm ▸ hInvCont.aestronglyMeasurable)
  have hfwd : Integrable (𝓕 g) := by
    convert hlogi.comp_neg using 1
    funext u
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  rw [mellin_eq_fourier, hlogeq, hgi.fourier_fourierInv_eq hfwd hgc.continuousAt]
  unfold g σ
  congr 1
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have ht : (2 : ℂ) * Real.pi * ((s.im / (2 * Real.pi) : ℝ) : ℂ) = s.im := by
    exact_mod_cast mul_div_cancel₀ s.im hπ
  rw [ht]
  exact Complex.re_add_im s

theorem quadraticHeckeDualProfile_mellin_half (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) :
    mellin (quadraticHeckeDualProfile A r w) (1 / 2) = mellin w (1 / 2) := by
  rw [quadraticHeckeDualProfile_mellin A r w hcompact hpositive hsmooth (1 / 2) (by norm_num),
    quadraticHeckeDualMellin_half]

end
end ArtinMatthews
