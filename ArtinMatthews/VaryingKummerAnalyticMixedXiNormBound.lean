module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaVertical
public import ArtinMatthews.VaryingKummerAnalyticDedekindLogDerivativeBound
public import ArtinMatthews.VaryingKummerAnalyticMixedXiLogDeriv
public import ArtinMatthews.VaryingKummerAnalyticMixedFunctionalNormalization
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale


set_option backward.privateInPublic true
@[expose] public section

/-! A field-uniform bound for the full complex logarithmic derivative of
the actual mixed-signature completed Dedekind xi function on Re(s)=2. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
noncomputable section
universe u

theorem mixedDiscriminantScale_log_abs_le_degree
    (K : Type u) [Field K] [NumberField K] :
    |Real.log (mixedDiscriminantScale K)| ≤ Real.log |(discr K : ℝ)|/2 +
      (Module.finrank ℚ K : ℝ)*Real.log 2 := by
  have hD := discr_log_nonneg K
  have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hr : (InfinitePlace.nrComplexPlaces K : ℝ) ≤ Module.finrank ℚ K := by
    exact_mod_cast (show InfinitePlace.nrComplexPlaces K ≤ Module.finrank ℚ K by
      have h := InfinitePlace.card_add_two_mul_card_eq_rank K
      omega)
  rw [mixedDiscriminantScale_log]
  calc
    _ ≤ |-(InfinitePlace.nrComplexPlaces K : ℝ)*Real.log 2| +
        |Real.log |(discr K : ℝ)|/2| := abs_add_le _ _
    _ = (InfinitePlace.nrComplexPlaces K : ℝ)*Real.log 2 +
        Real.log |(discr K : ℝ)|/2 := by
      rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hl),
        abs_of_nonneg (div_nonneg hD (by norm_num))]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hr hl]

private lemma norm_inverse_le_reciprocal_re {s : ℂ} (hs : 0 < s.re) :
    ‖(1 : ℂ)/s‖ ≤ 1/s.re := by
  simp only [norm_div, norm_one]
  exact one_div_le_one_div_of_le hs (Complex.re_le_norm s)

theorem exists_mixedCompletedDedekindXi_vertical_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ s : ℂ,
      s.re = 2 → ‖logDeriv (mixedCompletedDedekindXi K) s‖ ≤
        C*(Real.log |(discr K : ℝ)| +
          (Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2)) := by
  obtain ⟨B,hB,hgamma⟩ := exists_mixedGammaFactor_vertical_logarithmic_bound.{u}
  let E := dedekindLogDerivUniformConstant
  have hE : 0 < E := dedekindLogDerivUniformConstant_pos
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let A := (2+E)/Real.log 2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨B+A+2,by positivity,?_⟩
  intro K _ _ s hs
  have hd : 1 ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hd0 : 0 ≤ (Module.finrank ℚ K : ℝ) := by positivity
  have hD := discr_log_nonneg K
  have hl : Real.log 2 ≤ Real.log (|s.im|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hl0 : 0 ≤ Real.log (|s.im|+2) := hl2.le.trans hl
  have h₁ : ‖(1 : ℂ)/s‖ ≤ 1/2 := by
    simpa only [hs] using norm_inverse_le_reciprocal_re (show 0 < s.re by rw [hs]; norm_num)
  have h₂ : ‖(1 : ℂ)/(s-1)‖ ≤ 1 := by
    convert norm_inverse_le_reciprocal_re
      (show 0 < (s-1).re by simp [hs])
      using 1
    norm_num [hs]
  have hscale : ‖(Real.log (mixedDiscriminantScale K) : ℂ)‖ ≤
      Real.log |(discr K : ℝ)|/2 + (Module.finrank ℚ K : ℝ)*Real.log 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using mixedDiscriminantScale_log_abs_le_degree K
  have hγ := hgamma K s (by linarith) (by linarith)
  have hζ := dedekindZeta_logDeriv_norm_le K (show (3/2 : ℝ) ≤ s.re by linarith)
  have hraw : ‖logDeriv (mixedCompletedDedekindXi K) s‖ ≤
      3/2 + Real.log |(discr K : ℝ)|/2 + (Module.finrank ℚ K : ℝ)*Real.log 2 +
        B*(Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) + E*(Module.finrank ℚ K : ℝ) := by
    rw [mixedCompletedDedekindXi_logDeriv K (by linarith)]
    calc
      _ ≤ ‖1/s‖ + ‖1/(s-1)‖ + ‖(Real.log (mixedDiscriminantScale K) : ℂ)‖ +
          ‖logDeriv (mixedGammaFactor K) s‖ + ‖logDeriv (dedekindZeta K) s‖ := by
        have h₃ := norm_add_le ((1/s : ℂ)+1/(s-1)) (Real.log (mixedDiscriminantScale K) : ℂ)
        have h₄ := norm_add_le ((1/s : ℂ)+1/(s-1)+(Real.log (mixedDiscriminantScale K) : ℂ))
          (logDeriv (mixedGammaFactor K) s)
        have h₅ := norm_add_le ((1/s : ℂ)+1/(s-1)+(Real.log (mixedDiscriminantScale K) : ℂ)+
          logDeriv (mixedGammaFactor K) s) (logDeriv (dedekindZeta K) s)
        linarith [norm_add_le (1/s : ℂ) (1/(s-1))]
      _ ≤ _ := by linarith
  have hmass : 3/2 + E*(Module.finrank ℚ K : ℝ) ≤
      A*(Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) := by
    calc
      _ ≤ (2+E)*(Module.finrank ℚ K : ℝ) := by nlinarith
      _ = A*(Module.finrank ℚ K : ℝ)*Real.log 2 := by dsimp [A]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (mul_nonneg hA.le hd0)
  have hnlog := mul_le_mul_of_nonneg_left hl hd0
  have hCD := mul_nonneg (show 0 ≤ B+A+3/2 by positivity) hD
  nlinarith

theorem exists_mixedCompletedDedekindXi_height_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ T : ℝ,
      ‖logDeriv (mixedCompletedDedekindXi K) (⟨2,T⟩ : ℂ)‖ ≤
        C*(Real.log |(discr K : ℝ)| +
          (Module.finrank ℚ K : ℝ)*Real.log (|T|+2)) := by
  obtain ⟨C,hC,h⟩ := exists_mixedCompletedDedekindXi_vertical_norm_bound.{u}
  exact ⟨C,hC,fun K _ _ T => h K ⟨2,T⟩ rfl⟩

end
end ArtinMatthews.VaryingKummerAnalytic
