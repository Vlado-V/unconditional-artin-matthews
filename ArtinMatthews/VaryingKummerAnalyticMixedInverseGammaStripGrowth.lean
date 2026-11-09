module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaRatioGlobal


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine uniform-in-real-part growth bound for the reciprocal mixed
Gamma factor on the convexity strip. This follows from its actual logarithmic
derivative and Grönwall, with a bounded-height constant obtained by compactness. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
open scoped NumberField nonZeroDivisors Classical ComplexConjugate
noncomputable section

theorem mixedInverseGammaFactor_conj (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    mixedInverseGammaFactor K (conj s) = conj (mixedInverseGammaFactor K s) := by
  rw [mixedInverseGammaFactor,mixedGammaFactor_conj,mixedInverseGammaFactor,map_inv₀]

theorem mixedInverseGammaFactor_logDeriv_of_im_ne_zero
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : s.im ≠ 0) :
    logDeriv (mixedInverseGammaFactor K) s = -logDeriv (mixedGammaFactor K) s := by
  have hd := mixedGammaFactor_differentiableAt_of_im_ne_zero K hs
  have hn := mixedGammaFactor_ne_zero_of_im_ne_zero K hs
  have H := (hd.hasDerivAt.inv hn).deriv
  change deriv (fun z => (mixedGammaFactor K z)⁻¹) s = _ at H
  change logDeriv (fun z => (mixedGammaFactor K z)⁻¹) s = _
  rw [logDeriv_apply,H,logDeriv_apply]
  field_simp

theorem exists_mixedInverseGammaFactor_strip_growth
    (K : Type*) [Field K] [NumberField K] :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ σ : ℝ, -(1/4 : ℝ) ≤ σ → σ ≤ 5/4 →
      ∀ t : ℝ, 1 ≤ |t| →
        ‖mixedInverseGammaFactor K ((σ : ℂ)+(t : ℂ)*I)‖ ≤
          C*Real.exp (D*(|t|+2)^2) := by
  obtain ⟨B,hB,hbound⟩ := exists_mixedGammaFactor_high_strip_logarithmic_bound
  have hcurve : Continuous (fun σ : ℝ => ‖mixedInverseGammaFactor K ((σ : ℂ)+I)‖) := by
    exact ((mixedInverseGammaFactor_entire K).continuous.comp (by fun_prop)).norm
  obtain ⟨σ₀,_hσ₀,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-(1/4 : ℝ)) (5/4)).Nonempty from ⟨0,by norm_num⟩) hcurve.continuousOn
  let C := ‖mixedInverseGammaFactor K ((σ₀ : ℂ)+I)‖+1
  let D := B*(Module.finrank ℚ K : ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hpos (σ : ℝ) (hσ : -(1/4 : ℝ) ≤ σ) (hσ' : σ ≤ 5/4)
      (T : ℝ) (hT : 1 ≤ T) :
      ‖mixedInverseGammaFactor K ((σ : ℂ)+(T : ℂ)*I)‖ ≤ C*Real.exp (D*(T+2)^2) := by
    let F : ℝ → ℂ := fun x => mixedInverseGammaFactor K ((σ : ℂ)+(x : ℂ)*I)
    let F' : ℝ → ℂ := fun x => deriv (mixedInverseGammaFactor K) ((σ : ℂ)+(x : ℂ)*I)*I
    have hc : Continuous F := (mixedInverseGammaFactor_entire K).continuous.comp (by fun_prop)
    have hd (x : ℝ) : HasDerivAt F (F' x) x := by
      have H := (((mixedInverseGammaFactor_entire K) ((σ : ℂ)+(x : ℂ)*I)).hasDerivAt.comp
        (x : ℂ) (((hasDerivAt_id (x : ℂ)).mul_const I).const_add (σ : ℂ))).comp_ofReal
      simpa only [F,F',Function.comp_def,id_eq,one_mul] using H
    have hb (x : ℝ) (hx : x ∈ Ico 1 T) :
        ‖F' x‖ ≤ (B*(Module.finrank ℚ K : ℝ)*Real.log (T+2))*‖F x‖+0 := by
      have hi : ((σ : ℂ)+(x : ℂ)*I).im ≠ 0 := by
        simpa using (show x ≠ 0 by linarith [hx.1])
      have hn : mixedInverseGammaFactor K ((σ : ℂ)+(x : ℂ)*I) ≠ 0 :=
        inv_ne_zero (mixedGammaFactor_ne_zero_of_im_ne_zero K hi)
      have he : deriv (mixedInverseGammaFactor K) ((σ : ℂ)+(x : ℂ)*I) =
          logDeriv (mixedInverseGammaFactor K) ((σ : ℂ)+(x : ℂ)*I)*F x := by
        rw [logDeriv_apply,div_mul_cancel₀ _ hn]
      dsimp only [F']
      rw [norm_mul,norm_I,mul_one,he,norm_mul,
        mixedInverseGammaFactor_logDeriv_of_im_ne_zero K hi,norm_neg,add_zero]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have HG := hbound K ((σ : ℂ)+(x : ℂ)*I)
        (by simpa using (show -(1/2 : ℝ) ≤ σ by linarith))
        (by simpa using (show σ ≤ 2 by linarith))
        (by simpa [abs_of_nonneg (show 0 ≤ x by linarith [hx.1])] using hx.1)
      simp only [add_im,ofReal_im,ofReal_re,mul_im,I_im,I_re,mul_one,mul_zero,zero_add,add_zero] at HG
      rw [abs_of_nonneg (show 0 ≤ x by linarith [hx.1])] at HG
      apply HG.trans
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [hx.1]) (by linarith [hx.2]))
        (mul_nonneg hB.le (Nat.cast_nonneg _))
    have ha : ‖F 1‖ ≤ C := by
      have H := hmax (show σ ∈ Icc (-(1/4 : ℝ)) (5/4) from ⟨hσ,hσ'⟩)
      change ‖mixedInverseGammaFactor K ((σ : ℂ)+I)‖ ≤
        ‖mixedInverseGammaFactor K ((σ₀ : ℂ)+I)‖ at H
      dsimp only [F,C]
      simp only [ofReal_one,one_mul]
      linarith
    have H := norm_le_gronwallBound_of_norm_deriv_right_le hc.continuousOn
      (fun x _ => (hd x).hasDerivWithinAt) ha hb T ⟨hT,le_rfl⟩
    rw [gronwallBound_ε0] at H
    apply H.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    have hl : Real.log (T+2) ≤ T+2 := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hn : 0 ≤ B*(Module.finrank ℚ K : ℝ) := mul_nonneg hB.le (Nat.cast_nonneg _)
    dsimp [D]
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hl)]
  refine ⟨C,D,hC,hD,?_⟩
  intro σ hσ hσ' t ht
  by_cases htp : 0 ≤ t
  · simpa only [abs_of_nonneg htp] using hpos σ hσ hσ' t (by simpa only [abs_of_nonneg htp] using ht)
  · have htneg : t < 0 := lt_of_not_ge htp
    have he : (σ : ℂ)+((|t| : ℝ) : ℂ)*I = conj ((σ : ℂ)+(t : ℂ)*I) := by
      simp only [abs_of_neg htneg,ofReal_neg,map_add,map_mul,conj_ofReal,conj_I]
      ring
    have H := hpos σ hσ hσ' |t| ht
    rw [he,mixedInverseGammaFactor_conj,norm_conj] at H
    exact H

end
end ArtinMatthews.VaryingKummerAnalytic
