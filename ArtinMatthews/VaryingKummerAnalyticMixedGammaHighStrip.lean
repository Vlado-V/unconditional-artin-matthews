module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAway


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Gamma bounds throughout the contour strip at nonzero height. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped Classical BigOperators
noncomputable section
universe u

theorem gamma_argument_away_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n h
  have hi := congrArg Complex.im h
  simp only [Complex.neg_im, Complex.natCast_im, neg_zero] at hi
  exact hz hi

theorem mixedGammaAtom_high_strip_logarithmic_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, -(1/2 : ℝ) ≤ z.re → z.re ≤ 2 →
      (1/2 : ℝ) ≤ |z.im| → ‖logDeriv mixedGammaAtom z‖ ≤ B*Real.log (|z.im|+2) := by
  obtain ⟨C,hC,hbound⟩ := mixedGammaAtom_logarithmic_bound
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨C+2/Real.log 2,by positivity,?_⟩
  intro z hz hz' him
  have hl : Real.log 2 ≤ Real.log (|z.im|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg z.im])
  have hl0 : 0 ≤ Real.log (|z.im|+2) := hl2.le.trans hl
  have htwo : 2 ≤ (2/Real.log 2)*Real.log (|z.im|+2) := by
    have h := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2/Real.log 2 by positivity)
    rwa [div_mul_cancel₀ _ hl2.ne'] at h
  by_cases hpos : (1/2 : ℝ) ≤ z.re
  · have h := hbound z hpos hz'
    nlinarith
  have hp : (1/2 : ℝ) ≤ (z+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hp' : (z+1).re ≤ 2 := by simp only [Complex.add_re,Complex.one_re]; linarith
  have ha := gamma_argument_away_of_im_ne_zero
    (show z.im ≠ 0 by intro h; norm_num [h] at him)
  have hrec : logDeriv mixedGammaAtom z = logDeriv mixedGammaAtom (z+1) - 1/z := by
    rw [mixedGammaAtom_logDeriv_eq_away ha,
      mixedGammaAtom_logDeriv_eq (by linarith : 0 < (z+1).re),
      Complex.digamma_apply_add_one z ha]
    ring
  have h := hbound (z+1) hp hp'
  simp only [Complex.add_im,Complex.one_im,add_zero] at h
  have hinv : ‖(1 : ℂ)/z‖ ≤ 2 := by
    have hn := him.trans (Complex.abs_im_le_norm z)
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/2) hn
    simpa only [norm_div,norm_one] using (show 1/‖z‖ ≤ 2 by norm_num at hh ⊢; exact hh)
  rw [hrec]
  exact (norm_sub_le _ _).trans (by nlinarith)

theorem mixedGammaArgument_away_of_im_ne_zero
    (K : Type u) [Field K] [NumberField K] {s : ℂ} (hs : s.im ≠ 0)
    (w : InfinitePlace K) : ∀ n : ℕ, (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ) := by
  apply gamma_argument_away_of_im_ne_zero
  have hm : (InfinitePlace.mult w : ℝ) ≠ 0 := by
    exact_mod_cast InfinitePlace.mult_pos.ne'
  simpa using div_ne_zero (mul_ne_zero hm hs) (by norm_num : (2 : ℝ) ≠ 0)

theorem exists_mixedGammaFactor_high_strip_logarithmic_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K],
      ∀ s : ℂ, -(1/2 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
        ‖logDeriv (mixedGammaFactor K) s‖ ≤
          B*(Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) := by
  obtain ⟨B,hB,hbound⟩ := mixedGammaAtom_high_strip_logarithmic_bound
  refine ⟨B,hB,?_⟩
  intro K _ _ s hs hs' him
  have hm₀ (w : InfinitePlace K) : (0 : ℝ) ≤ InfinitePlace.mult w := Nat.cast_nonneg _
  have hm₁ (w : InfinitePlace K) : (1 : ℝ) ≤ InfinitePlace.mult w := InfinitePlace.one_le_mult
  have hm₂ (w : InfinitePlace K) : (InfinitePlace.mult w : ℝ) ≤ 2 := by
    unfold InfinitePlace.mult
    split_ifs <;> norm_num
  have hre (w : InfinitePlace K) :
      (((InfinitePlace.mult w : ℂ)*s/2).re) = (InfinitePlace.mult w : ℝ)*s.re/2 := by simp
  have hi (w : InfinitePlace K) :
      |((InfinitePlace.mult w : ℂ)*s/2).im| = (InfinitePlace.mult w : ℝ)*|s.im|/2 := by
    simp only [Complex.div_ofNat_im, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero, abs_div, abs_mul,
      abs_of_nonneg (hm₀ w)]
    norm_num
  have ha := mixedGammaArgument_away_of_im_ne_zero K
    (show s.im ≠ 0 by intro h; norm_num [h] at him)
  have hb (w : InfinitePlace K) :
      ‖logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2)‖ ≤ B*Real.log (|s.im|+2) := by
    have harg₁ : -(1/2 : ℝ) ≤ ((InfinitePlace.mult w : ℂ)*s/2).re := by
      rw [hre]
      nlinarith [mul_le_mul_of_nonneg_left hs (hm₀ w),hm₂ w]
    have harg₂ : ((InfinitePlace.mult w : ℂ)*s/2).re ≤ 2 := by
      rw [hre]
      nlinarith [mul_le_mul_of_nonneg_left hs' (hm₀ w),hm₂ w]
    have harg₃ : (1/2 : ℝ) ≤ |((InfinitePlace.mult w : ℂ)*s/2).im| := by
      rw [hi]
      nlinarith [mul_le_mul_of_nonneg_left him (hm₀ w),hm₁ w]
    apply (hbound _ harg₁ harg₂ harg₃).trans
    apply mul_le_mul_of_nonneg_left _ hB.le
    apply Real.log_le_log (by positivity)
    rw [hi]
    nlinarith [mul_le_mul_of_nonneg_right (hm₂ w) (abs_nonneg s.im)]
  apply (mixedGammaFactor_logDeriv_norm_le_of_bounds_away K ha hb).trans
  have hl : 0 ≤ Real.log (|s.im|+2) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  have hn : 0 ≤ (Module.finrank ℚ K : ℝ) := by positivity
  nlinarith [mul_nonneg hn (mul_nonneg hB.le hl)]

end
end ArtinMatthews.VaryingKummerAnalytic
