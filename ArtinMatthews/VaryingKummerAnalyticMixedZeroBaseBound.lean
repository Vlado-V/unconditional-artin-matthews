module

public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale
public import ArtinMatthews.VaryingKummerAnalyticMixedXiZeroStrip
public import ArtinMatthews.VaryingKummerAnalyticMixedXiLogDerivBase
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaLogDerivBound
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishingLogDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine discriminant-and-degree-uniform logarithmic-derivative bound for
Dedekind xi, and its concrete padded zero-analysis scale. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
open scoped Classical
noncomputable section
universe u
variable (K : Type u) [Field K] [NumberField K]

theorem mixedCompletedDedekindXi_logDeriv_base_le {C L : ℝ}
    (hL : 1 ≤ L)
    (hGamma : ∀ σ : ℝ, σ ∈ Icc (1:ℝ) 2 →
      ‖logDeriv (mixedGammaFactor K) (σ : ℂ)‖ ≤ C*(Module.finrank ℚ K : ℝ)) :
    (logDeriv (mixedCompletedDedekindXi K) ((1+1/L : ℝ) : ℂ)).re ≤
      L + 1 + Real.log |(discr K : ℝ)|/2 + C*(Module.finrank ℚ K : ℝ) := by
  let σ : ℝ := 1+1/L
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hs : 1 < σ := by dsimp [σ]; linarith [one_div_pos.mpr hL0]
  have hs2 : σ ≤ 2 := by
    have hh : 1/L ≤ 1 := (div_le_one hL0).mpr hL
    dsimp [σ]
    linarith
  have hΓ := (Complex.re_le_norm (logDeriv (mixedGammaFactor K) (σ : ℂ))).trans
    (hGamma σ ⟨hs.le,hs2⟩)
  have hζ := dedekindZeta_logDeriv_re_nonpos K hs
  have hlog := mixedDiscriminantScale_log_le K
  have hrec : (1/(σ : ℂ)).re ≤ 1 := by
    have he : (1/(σ : ℂ)).re = 1/σ := by norm_cast
    rw [he]
    exact (div_le_one (lt_trans zero_lt_one hs)).mpr hs.le
  have hsing : (1/((σ : ℂ)-1)).re = L := by
    have he : (σ : ℂ)-1 = ((1/L : ℝ) : ℂ) := by dsimp [σ]; push_cast; ring
    rw [he]
    norm_cast
    simp
  have H := congrArg Complex.re (mixedCompletedDedekindXi_logDeriv_of_zeta_ne_zero K
    (s := (σ : ℂ)) hs (dedekindZeta_ne_zero_of_one_lt_re K hs))
  simp only [Complex.add_re, Complex.ofReal_re] at H
  rw [hsing] at H
  change (logDeriv (mixedCompletedDedekindXi K) (σ : ℂ)).re ≤ _
  linarith

theorem mixedCompletedDedekindXi_logDeriv_at_zeroScale {C : ℝ} (hC : 0 ≤ C)
    (hGamma : ∀ σ : ℝ, σ ∈ Icc (1:ℝ) 2 →
      ‖logDeriv (mixedGammaFactor K) (σ : ℂ)‖ ≤ C*(Module.finrank ℚ K : ℝ)) :
    (logDeriv (mixedCompletedDedekindXi K)
      ((1+1/mixedZeroScale K C : ℝ) : ℂ)).re ≤ (3/2)*mixedZeroScale K C := by
  have H := mixedCompletedDedekindXi_logDeriv_base_le K
    (show 1 ≤ mixedZeroScale K C by linarith [mixedZeroScale_two_le K hC]) hGamma
  unfold mixedZeroScale at H ⊢
  linarith

/-- The constant is universal across all number fields; the scale carries the
actual discriminant and degree dependence. -/
theorem exists_mixedCompletedDedekindXi_zeroScale_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K],
      (logDeriv (mixedCompletedDedekindXi K)
        ((1+1/mixedZeroScale K C : ℝ) : ℂ)).re ≤ (3/2)*mixedZeroScale K C := by
  obtain ⟨C,hC,hΓ⟩ := exists_mixedGammaFactor_logDeriv_bound.{u}
  exact ⟨C,hC,fun K _ _ => mixedCompletedDedekindXi_logDeriv_at_zeroScale K hC.le (hΓ K)⟩

end
end ArtinMatthews.VaryingKummerAnalytic
