module

public import ArtinMatthews.SpectralExpPolynomialConvergence
public import ArtinMatthews.SpectralJGaussianDecay
public import ArtinMatthews.SpectralJGaussianPolynomialCoefficient
public import ArtinMatthews.SpectralJGaussianProfileError


set_option backward.privateInPublic true
@[expose] public section

/-! The literal real-order coefficient for every smooth compact positive test. -/
namespace ArtinMatthews
open MeasureTheory Set OAI.CubicEisenstein
open scoped ContDiff
noncomputable section

theorem spectralJGaussianTail_real_integrable (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) (r : ℝ) :
    IntegrableOn (fun y : ℝ =>
      spectralJGaussianTail (spectralJGaussianTransform f) y *
        schlafliBesselK ((r : ℂ) * Complex.I) y / (y : ℂ)) (Ioi 0) := by
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) :=
    (hf.continuous.integrable_of_hasCompactSupport hfc).integrableOn
  obtain ⟨B, hB, hb⟩ := spectralJGaussianTransform_linear_decay f hf hfc hpos
  exact spectralJGaussianTail_KLIntegral_integrable _
    (spectralJGaussianTransform_continuous f hf.continuous hfi).measurable B hB
    (fun w hw => hb w (by linarith)) r

theorem spectralWeylJMultiplier_compact_integrable (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hpos : tsupport f ⊆ Ioi (0 : ℝ)) (r : ℝ) :
    IntegrableOn (fun x : ℝ => f x * spectralWeylJMultiplier r x) (Ioi 0) := by
  let g := spectralSquareProfile f
  have hg : Continuous g := (spectralSquareProfile_contDiff hf hpos).continuous
  have hs := spectralSquareProfile_support hfc hpos
  obtain ⟨_, _, hb⟩ := spectralWeylJMultiplier_profile_bound r
  have hI := (hb g hg.measurable
    (spectralJCompactProfile_norm_div_sqrt_integrable hg hs.1 hs.2)).1
  apply hI.congr_fun _ measurableSet_Ioi
  intro x hx
  dsimp only
  change ((x : ℂ) * spectralSquareProfile f (x ^ 2)) * spectralWeylJMultiplier r x =
    f x * spectralWeylJMultiplier r x
  rw [spectralSquareProfile_recovery f (mem_Ioi.mp hx)]

theorem spectralJGaussianTail_real_coefficient_raw (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ))
    (r : ℝ) (hr : 0 < r) :
    spectralJRawKLCoefficient (spectralJGaussianTransform f) r =
      ((Real.sqrt (8 * Real.pi) : ℂ) / (4 * (Real.cosh (Real.pi * r) : ℂ))) *
        ∫ x : ℝ in Ioi 0, f x * spectralWeylJMultiplier r x := by
  let R (u : ℝ → ℂ) := ∫ x : ℝ in Ioi 0, u x * spectralWeylJMultiplier r x
  let L (u : ℝ → ℂ) := spectralJRawKLCoefficient (spectralJGaussianTransform u) r
  let c := (Real.sqrt (8 * Real.pi) : ℂ) / (4 * (Real.cosh (Real.pi * r) : ℂ))
  let g := spectralSquareProfile f
  have hg : ContDiff ℝ ∞ g := spectralSquareProfile_contDiff hf hpos
  have hgc : HasCompactSupport g := (spectralSquareProfile_support hfc hpos).1
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) :=
    (hf.continuous.integrable_of_hasCompactSupport hfc).integrableOn
  have hFm := (spectralJGaussianTransform_continuous f hf.continuous hfi).measurable
  obtain ⟨B, hB, hF⟩ := spectralJGaussianTransform_linear_decay f (hf.of_le (by simp)) hfc hpos
  have hRi := spectralWeylJMultiplier_compact_integrable f hf hfc hpos r
  obtain ⟨A, hA, herror⟩ := spectralJGaussianTransform_exp_error_bound
  obtain ⟨D, hD, hright⟩ := spectralWeylJMultiplier_profile_bound r
  let M := spectralJTailKZeroMellinMass
  let C := ‖c‖ * D * Real.sqrt Real.pi + 4 * M * A
  have hM : 0 ≤ M := spectralJTailKZeroMellinMass_nonneg
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg c) hD) (Real.sqrt_nonneg _))
    (mul_nonneg (mul_nonneg (by norm_num) hM) hA.le)
  have herr (ε : ℝ) (hε : 0 < ε) : ‖L f - c * R f‖ ≤ C * ε := by
    obtain ⟨p, hd, henv⟩ := exists_spectralExpPolynomial_diff_envelope g hg hgc hε
    let d (s : ℝ) := spectralExpPolynomial p s - g s
    let v (x : ℝ) := (x : ℂ) * d (x ^ 2)
    let fp (x : ℝ) := (x : ℂ) * spectralExpPolynomial p (x ^ 2)
    obtain ⟨hvi, hVm, hV⟩ := herror d hd ε hε.le henv
    have hLp : ‖L v‖ ≤ 4 * M * (A * ε) :=
      spectralJGaussianTail_KLIntegral_norm_le _ hVm (A * ε) (mul_nonneg hA.le hε.le)
        (fun w hw => hV w (by linarith)) r
    have hL1 := (spectralExpEnvelope_weightedL1 hd henv).1
    obtain ⟨hRvi, hRvp⟩ := hright d hd.continuous.measurable hL1.1
    have hRp : ‖R v‖ ≤ D * (ε * Real.sqrt Real.pi) :=
      hRvp.trans (mul_le_mul_of_nonneg_left hL1.2 hD)
    have hsum : EqOn fp (fun x => f x + v x) (Ioi (0 : ℝ)) := by
      intro x hx
      have hrec : (x : ℂ) * g (x ^ 2) = f x :=
        spectralSquareProfile_recovery f (mem_Ioi.mp hx)
      change (x : ℂ) * spectralExpPolynomial p (x ^ 2) =
        f x + (x : ℂ) * (spectralExpPolynomial p (x ^ 2) - g (x ^ 2))
      rw [← hrec]
      ring
    have hFp : spectralJGaussianTransform fp = fun w =>
        spectralJGaussianTransform f w + spectralJGaussianTransform v w :=
      (spectralJGaussianTransform_congr_Ioi hsum).trans (spectralJGaussianTransform_add f v hfi hvi)
    have hLadd : L fp = L f + L v := by
      dsimp only [L]
      rw [hFp]
      exact spectralJRawKLCoefficient_add _ _ hFm hVm B (A * ε) hB (mul_nonneg hA.le hε.le)
        (fun w hw => hF w (by linarith)) (fun w hw => hV w (by linarith)) r
    have hRadd : R fp = R f + R v := calc
      _ = ∫ x : ℝ in Ioi 0, (f x + v x) * spectralWeylJMultiplier r x :=
        setIntegral_congr_fun measurableSet_Ioi
          (fun x hx => congrArg (fun z : ℂ => z * spectralWeylJMultiplier r x) (hsum hx))
      _ = _ := by
        simp only [add_mul]
        exact integral_add hRi hRvi
    have htest : L fp = c * R fp := spectralJGaussianPolynomial_raw_coefficient p r hr
    rw [hLadd, hRadd] at htest
    have hdiff : L f - c * R f = c * R v - L v := by linear_combination htest
    calc
      _ = ‖c * R v - L v‖ := congrArg norm hdiff
      _ ≤ ‖c‖ * ‖R v‖ + ‖L v‖ := by
        rw [← norm_mul]
        exact norm_sub_le _ _
      _ ≤ ‖c‖ * (D * (ε * Real.sqrt Real.pi)) + 4 * M * (A * ε) :=
        add_le_add (mul_le_mul_of_nonneg_left hRp (norm_nonneg _)) hLp
      _ = C * ε := by dsimp only [C]; ring
  have hz : ‖L f - c * R f‖ ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hden : 0 < C + 1 := add_pos_of_nonneg_of_pos hC zero_lt_one
    refine (herr (δ / (C + 1)) (div_pos hδ hden)).trans ?_
    rw [zero_add, ← mul_div_assoc]
    exact (div_le_iff₀ hden).mpr (by nlinarith)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

theorem spectralJGaussianTail_real_coefficient (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ))
    (r : ℝ) (hr : 0 < r) :
    (∫ y : ℝ in Ioi 0, spectralJGaussianTail (spectralJGaussianTransform f) y *
      schlafliBesselK ((r : ℂ) * Complex.I) y / (y : ℂ)) / (Real.sqrt (8 * Real.pi) : ℂ) =
    (∫ x : ℝ in Ioi 0, f x * spectralWeylJMultiplier r x) / (4 * (Real.cosh (Real.pi * r) : ℂ)) := by
  change spectralJRawKLCoefficient (spectralJGaussianTransform f) r /
    (Real.sqrt (8 * Real.pi) : ℂ) = _
  rw [spectralJGaussianTail_real_coefficient_raw f hf hfc hpos r hr]
  have h : (Real.sqrt (8 * Real.pi) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [show ((Real.sqrt (8 * Real.pi) : ℂ) / (4 * (Real.cosh (Real.pi * r) : ℂ))) *
      (∫ x : ℝ in Ioi 0, f x * spectralWeylJMultiplier r x) =
      (Real.sqrt (8 * Real.pi) : ℂ) *
        ((∫ x : ℝ in Ioi 0, f x * spectralWeylJMultiplier r x) /
          (4 * (Real.cosh (Real.pi * r) : ℂ))) by ring]
  exact mul_div_cancel_left₀ _ h

end
end ArtinMatthews
