module

public import ArtinMatthews.VaryingKummerAnalyticMixedZeroHeightCount
public import ArtinMatthews.VaryingKummerAnalyticMixedXiLogDeriv
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaVertical
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale


set_option backward.privateInPublic true
@[expose] public section

/-! The exact remaining input to the quantitative height-window zero bound:
the norm of the actual Dedekind logarithmic derivative on Re(s)=2. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField Complex
open OAI.PrimeDegreePackets.AnalyticGrowth
noncomputable section
universe u

lemma inverse_re_le_reciprocal_re {z : ℂ} (hz : 0 < z.re) :
    (1/z).re ≤ 1/z.re := by
  calc
    _ ≤ ‖(1 : ℂ)/z‖ := Complex.re_le_norm _
    _ = 1/‖z‖ := by simp
    _ ≤ _ := one_div_le_one_div_of_le hz (Complex.re_le_norm z)

theorem exists_mixedCompletedDedekindXi_height_base_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ T : ℝ,
      (logDeriv (mixedCompletedDedekindXi K) (⟨2,T⟩ : ℂ)).re ≤
        3/2 + Real.log |(discr K : ℝ)|/2 +
          B*(Module.finrank ℚ K : ℝ)*Real.log (|T|+2) +
            ‖logDeriv (dedekindZeta K) (⟨2,T⟩ : ℂ)‖ := by
  obtain ⟨B,hB,hgamma⟩ := exists_mixedGammaFactor_vertical_logarithmic_bound
  refine ⟨B,hB,?_⟩
  intro K _ _ T
  have h₁ : (1/(⟨2,T⟩ : ℂ)).re ≤ 1/2 :=
    inverse_re_le_reciprocal_re (by norm_num)
  have h₂ : (1/((⟨2,T⟩ : ℂ)-1)).re ≤ 1 := by
    calc
      _ ≤ 1/((⟨2,T⟩ : ℂ)-1).re := inverse_re_le_reciprocal_re (by norm_num)
      _ = 1 := by norm_num
  have hγ := (Complex.re_le_norm (logDeriv (mixedGammaFactor K) (⟨2,T⟩ : ℂ))).trans
    (hgamma K (⟨2,T⟩ : ℂ) (by norm_num) (by norm_num))
  have hζ := Complex.re_le_norm (logDeriv (dedekindZeta K) (⟨2,T⟩ : ℂ))
  have hd := mixedDiscriminantScale_log_le K
  rw [mixedCompletedDedekindXi_logDeriv_re K (by norm_num)]
  change _ ≤ 3/2 + Real.log |(discr K : ℝ)|/2 +
    B*(Module.finrank ℚ K : ℝ)*Real.log (|T|+2) + _
  change _ ≤ B*(Module.finrank ℚ K : ℝ)*Real.log (|T|+2) at hγ
  linarith

theorem exists_mixedDedekind_zeroHeight_bound_with_logDeriv :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ T : ℝ,
      zeroHeightCount (mixedCompletedDedekindXi K) T ≤
        15/2 + (5/2)*Real.log |(discr K : ℝ)| +
          B*(Module.finrank ℚ K : ℝ)*Real.log (|T|+2) +
            5*‖logDeriv (dedekindZeta K) (⟨2,T⟩ : ℂ)‖ := by
  obtain ⟨B,hB,hbound⟩ := exists_mixedCompletedDedekindXi_height_base_bound
  refine ⟨5*B,by positivity,?_⟩
  intro K _ _ T
  have H := mixedCompletedDedekindXi_zeroHeightCount_le_logDeriv K T
  have H' := hbound K T
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
