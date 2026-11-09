module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaRatioGlobal


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Gamma ratio at `Re(s) = -0.001`, with the same polynomial
height degree as the wider Gamma strip. No asymptotic gamma premise is
added: the high part uses the existing logarithmic derivative bound. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField Complex Set VaryingKummerAnalytic
open scoped Classical ComplexConjugate
noncomputable section
variable (F : Type) [Field F] [NumberField F]

def sourceNarrowGammaRatio (t : ℝ) : ℂ :=
  mixedGammaFactor F ((1001/1000 : ℂ) - (t : ℂ)*I) *
    mixedInverseGammaFactor F ((-1/1000 : ℂ) + (t : ℂ)*I)

theorem sourceNarrowGammaRatio_norm (t : ℝ) :
    ‖sourceNarrowGammaRatio F t‖ =
      ‖mixedGammaFactor F ((1001/1000 : ℂ) + (t : ℂ)*I) *
        mixedInverseGammaFactor F ((-1/1000 : ℂ) + (t : ℂ)*I)‖ := by
  have he : ((1001/1000 : ℂ) - (t : ℂ)*I) = conj ((1001/1000 : ℂ) + (t : ℂ)*I) := by
    simp only [map_add, map_div₀, map_ofNat, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [sourceNarrowGammaRatio, he, mixedGammaFactor_conj, norm_mul, norm_mul, norm_conj]

theorem sourceNarrowGammaRatio_continuous : Continuous (sourceNarrowGammaRatio F) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hG := (mixedGammaFactor_differentiableAt F
    (s := (1001/1000 : ℂ) - (t : ℂ)*I) (by norm_num)).continuousAt
  have hi := (mixedInverseGammaFactor_entire F ((-1/1000 : ℂ) + (t : ℂ)*I)).continuousAt
  exact (hG.comp (f := fun u : ℝ => (1001/1000 : ℂ) - (u : ℂ)*I) (by fun_prop)).mul
    (hi.comp (f := fun u : ℝ => (-1/1000 : ℂ) + (u : ℂ)*I) (by fun_prop))

theorem sourceNarrowGammaRatio_polynomial_high :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖sourceNarrowGammaRatio F t‖ ≤ (|t|+2)^(B*(Module.finrank ℚ F : ℝ)) := by
  obtain ⟨B, hB, hbound⟩ := exists_mixedGammaFactor_high_strip_logarithmic_bound
  refine ⟨2*B, by positivity, ?_⟩
  intro t ht
  have htz : t ≠ 0 := by intro h; norm_num [h] at ht
  have him (x : ℝ) : ((x : ℂ)+(t : ℂ)*I).im ≠ 0 := by simpa using htz
  have H := horizontal_ratio_le_exp_logDeriv_bound
    (f := mixedGammaFactor F) (a := -1/1000) (b := 1001/1000) (t := t)
    (C := B*(Module.finrank ℚ F : ℝ)*Real.log (|t|+2)) (by norm_num)
    (fun x _ => mixedGammaFactor_differentiableAt_of_im_ne_zero F (him x))
    (fun x _ => mixedGammaFactor_ne_zero_of_im_ne_zero F (him x))
    (fun x hx => by
      have H := hbound F ((x : ℂ)+(t : ℂ)*I)
        (by simpa using (show -(1/2 : ℝ) ≤ x by linarith [hx.1]))
        (by simpa using (show x ≤ 2 by linarith [hx.2])) (by simpa using ht)
      simpa using H)
  rw [sourceNarrowGammaRatio_norm]
  push_cast at H
  change ‖mixedGammaFactor F ((1001/1000 : ℂ)+(t : ℂ)*I) *
    (mixedGammaFactor F ((-1/1000 : ℂ)+(t : ℂ)*I))⁻¹‖ ≤ _
  apply H.trans
  rw [Real.rpow_def_of_pos (by linarith [abs_nonneg t])]
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ B*(Module.finrank ℚ F : ℝ)*Real.log (|t|+2) := by
    exact mul_nonneg (mul_nonneg hB.le (Nat.cast_nonneg _)) (Real.log_nonneg (by linarith))
  linarith only [h]

theorem exists_sourceNarrowGammaRatio_polynomial_bound :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧ ∀ t : ℝ, ‖sourceNarrowGammaRatio F t‖ ≤ C*(|t|+2)^m := by
  obtain ⟨B, _, hbound⟩ := sourceNarrowGammaRatio_polynomial_high F
  obtain ⟨t₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
    (sourceNarrowGammaRatio_continuous F).norm.continuousOn
  let C := ‖sourceNarrowGammaRatio F t₀‖+1
  let m := Nat.ceil (B*(Module.finrank ℚ F : ℝ))
  refine ⟨C, m, by dsimp [C]; positivity, ?_⟩
  intro t
  have hC : 1 ≤ C := by dsimp [C]; linarith [norm_nonneg (sourceNarrowGammaRatio F t₀)]
  have hp : 1 ≤ (|t|+2)^m := one_le_pow₀ (by linarith [abs_nonneg t])
  by_cases ht : 1 ≤ |t|
  · calc
      _ ≤ (|t|+2)^(B*(Module.finrank ℚ F : ℝ)) := hbound t ht
      _ ≤ (|t|+2)^m := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (Nat.le_ceil _)
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hC
  · have hm : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp (le_of_lt (lt_of_not_ge ht))
    exact (hmax hm).trans ((show ‖sourceNarrowGammaRatio F t₀‖ ≤ C by dsimp [C]; linarith).trans
      (le_mul_of_one_le_right (zero_le_one.trans hC) hp))

end
end ArtinMatthews.SourceEulerAssembly
