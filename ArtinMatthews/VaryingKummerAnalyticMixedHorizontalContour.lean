module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaGoodSequence
public import ArtinMatthews.VaryingKummerAnalyticMixedMellinResidues
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Vanishing of both actual horizontal Mellin contour integrals along
genuine symmetric zero-avoiding heights. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex MeasureTheory Set Filter
open scoped Topology ContDiff
noncomputable section
universe u

theorem norm_cpow_explicitFormula_strip_le {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : -(1/2 : ℝ) ≤ s.re) (hs' : s.re ≤ 2) :
    ‖(x : ℂ)^s‖ ≤ max (x ^ (-(1/2 : ℝ))) (x ^ (2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  by_cases h : x ≤ 1
  · exact (Real.rpow_le_rpow_of_exponent_ge hx h hs).trans (le_max_left _ _)
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hs').trans (le_max_right _ _)

private theorem explicitFormula_norm_high_bound
    (K : Type u) [Field K] [NumberField K] (f : ℝ → ℂ) {x A C : ℝ}
    (hx : 0 < x) (hA : 0 < A) (hC : 0 < C)
    (hM : ∀ s : ℂ, -(1/2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖mellin f s‖ ≤ A/(1+|s.im|)^4)
    (n : ℕ) {s : ℂ} (hs : -(1/2 : ℝ) ≤ s.re) (hs' : s.re ≤ 2)
    (him : (n : ℝ)+2 ≤ |s.im|)
    (hζ : ‖logDeriv (mixedDedekindZeta K) s‖ ≤ C*((n : ℝ)+3)^2) :
    ‖mixedExplicitFormulaIntegrand K f x s‖ ≤
      (A*max (x ^ (-(1/2 : ℝ))) (x ^ (2 : ℝ))*C)/((n : ℝ)+3)^2 := by
  let X := max (x ^ (-(1/2 : ℝ))) (x ^ (2 : ℝ))
  have hX : 0 ≤ X := (Real.rpow_pos_of_pos hx _).le.trans (le_max_left _ _)
  have hN : 0 < (n : ℝ)+3 := by positivity
  have hpow : ‖(x : ℂ)^s‖ ≤ X := norm_cpow_explicitFormula_strip_le hx hs hs'
  have hm : ‖mellin f s‖ ≤ A/((n : ℝ)+3)^4 := by
    apply (hM s hs hs').trans
    apply div_le_div_of_nonneg_left hA.le (pow_pos hN _) _
    exact pow_le_pow_left₀ hN.le (by linarith) 4
  rw [mixedExplicitFormulaIntegrand,norm_mul,norm_neg,norm_mul]
  calc
    _ ≤ (A/((n : ℝ)+3)^4)*X*(C*((n : ℝ)+3)^2) := by
      exact mul_le_mul (mul_le_mul hm hpow (norm_nonneg _) (by positivity)) hζ
        (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [X]; field_simp

theorem exists_mixedMellin_horizontal_integrals_tendsto_zero
    (K : Type u) [Field K] [NumberField K]
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f)
    {x : ℝ} (hx : 0 < x) :
    ∃ t : ℕ → ℝ,
      (∀ n : ℕ, t n ∈ Icc ((n : ℝ)+2) ((n : ℝ)+3)) ∧
      Tendsto t atTop atTop ∧
      (∀ (n : ℕ) (ρ : ℂ), mixedCompletedDedekindXi K ρ = 0 → |ρ.im| ≠ t n) ∧
      Tendsto (fun n => ∫ σ in (-(1/2 : ℝ))..2,
        mixedExplicitFormulaIntegrand K f x (⟨σ,t n⟩ : ℂ)) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ σ in (-(1/2 : ℝ))..2,
        mixedExplicitFormulaIntegrand K f x (⟨σ,-t n⟩ : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C,hC,t,ht,htlim,havoid,hbound⟩ := exists_mixedDedekindZeta_good_sequence K
  obtain ⟨A,hA,hM⟩ := smoothMellin_explicitFormula_decay f hcompact hpositive hsmooth 4
  let D := (A*max (x ^ (-(1/2 : ℝ))) (x ^ (2 : ℝ))*C)*(5/2)
  have hD : 0 ≤ D := by
    have hX : 0 < max (x ^ (-(1/2 : ℝ))) (x ^ (2 : ℝ)) :=
      (Real.rpow_pos_of_pos hx _).trans_le (le_max_left _ _)
    dsimp [D]
    positivity
  have hlim : Tendsto (fun n : ℕ => D/((n : ℝ)+3)^2) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)+3) atTop atTop :=
      tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop
    have hi := (tendsto_inv_atTop_zero.comp hn).pow 2
    simpa only [Function.comp_apply,inv_pow,div_eq_mul_inv,mul_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      hi.const_mul D
  refine ⟨t,ht,htlim,havoid,?_,?_⟩
  · apply squeeze_zero_norm (fun n => ?_) hlim
    have H := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(1/2 : ℝ)) (b := 2)
      (C := (A*max (x ^ (-(1/2 : ℝ))) (x ^ (2 : ℝ))*C)/((n : ℝ)+3)^2)
      (f := fun σ => mixedExplicitFormulaIntegrand K f x (⟨σ,t n⟩ : ℂ)) ?_
    · rw [show |(2 : ℝ) - -(1/2)| = 5/2 by norm_num] at H
      simpa only [D,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using H
    intro σ hσ
    rw [uIoc_of_le (by norm_num : -(1/2 : ℝ) ≤ 2)] at hσ
    apply explicitFormula_norm_high_bound K f hx hA hC hM n hσ.1.le hσ.2
    · change (n : ℝ)+2 ≤ |t n|
      exact (ht n).1.trans (le_abs_self _)
    · exact (hbound n σ hσ.1.le hσ.2).1
  · apply squeeze_zero_norm (fun n => ?_) hlim
    have H := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(1/2 : ℝ)) (b := 2)
      (C := (A*max (x ^ (-(1/2 : ℝ))) (x ^ (2 : ℝ))*C)/((n : ℝ)+3)^2)
      (f := fun σ => mixedExplicitFormulaIntegrand K f x (⟨σ,-t n⟩ : ℂ)) ?_
    · rw [show |(2 : ℝ) - -(1/2)| = 5/2 by norm_num] at H
      simpa only [D,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using H
    intro σ hσ
    rw [uIoc_of_le (by norm_num : -(1/2 : ℝ) ≤ 2)] at hσ
    apply explicitFormula_norm_high_bound K f hx hA hC hM n hσ.1.le hσ.2
    · change (n : ℝ)+2 ≤ |-t n|
      rw [abs_neg]
      exact (ht n).1.trans (le_abs_self _)
    · exact (hbound n σ hσ.1.le hσ.2).2

end
end ArtinMatthews.VaryingKummerAnalytic
