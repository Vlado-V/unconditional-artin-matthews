module

public import ArtinMatthews.SourceLocalCorrectionFactorization
public import ArtinMatthews.SourceExteriorRayEuler


set_option backward.privateInPublic true
@[expose] public section

/-! Actual norm-summable exterior Euler factors on Re(s)>1. The
logarithm stays in its disc at 1, so the products are nonzero and
can be inverted without a product or branch hypothesis. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]

theorem sourcePrimeNormRpow_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun P : ProbePrime F => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ)) := by
  have h := HeckeIdealMobius.normSeries_summable F (show 0 < σ - 1 by linarith)
  rw [show 1 + (σ - 1) = σ by ring] at h
  exact h.comp_injective
    (i := fun P : ProbePrime F => (⟨P.asIdeal, P.ne_bot⟩ : {I : Ideal (𝓞 F) // I ≠ ⊥}))
    (fun P Q he => HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val he))

def sourcePrimeEulerRatio (P : ProbePrime F) (a s : ℂ) : ℂ :=
  a * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)

theorem sourcePrimeEulerRatio_norm_le (P : ProbePrime F) (a s : ℂ) (ha : ‖a‖ ≤ 1) :
    ‖sourcePrimeEulerRatio F P a s‖ ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
  have hQ : 0 < (Ideal.absNorm P.asIdeal : ℝ) :=
    lt_trans zero_lt_one (probeIdealPrime_norm_gt_one F P)
  unfold sourcePrimeEulerRatio
  rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hQ, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hQ.le _) ha

theorem sourcePrimeEulerRatio_norm_le_half (P : ProbePrime F) (a s : ℂ) (ha : ‖a‖ ≤ 1)
    (hs : 1 ≤ s.re) : ‖sourcePrimeEulerRatio F P a s‖ ≤ 1 / 2 := by
  let Q : ℝ := Ideal.absNorm P.asIdeal
  have hQ : 1 < Q := probeIdealPrime_norm_gt_one F P
  have hQ2 : 2 ≤ Q := by
    have hN : 1 < Ideal.absNorm P.asIdeal := by
      dsimp only [Q] at hQ
      exact_mod_cast hQ
    dsimp only [Q]
    exact_mod_cast (show 2 ≤ Ideal.absNorm P.asIdeal by omega)
  calc
    _ ≤ Q ^ (-s.re) := sourcePrimeEulerRatio_norm_le F P a s ha
    _ ≤ Q ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hQ.le (neg_le_neg hs)
    _ = Q⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hQ2

theorem sourcePrimeEulerLog_norm_le (P : ProbePrime F) (a s : ℂ) (ha : ‖a‖ ≤ 1)
    (hs : 1 ≤ s.re) : ‖-Complex.log (1 - sourcePrimeEulerRatio F P a s)‖ ≤
      (3 / 2 : ℝ) * (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
  have h := Complex.norm_log_one_add_half_le_self (z := -sourcePrimeEulerRatio F P a s)
    (by rw [norm_neg]; exact sourcePrimeEulerRatio_norm_le_half F P a s ha hs)
  simp only [norm_neg, ← sub_eq_add_neg] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_left (sourcePrimeEulerRatio_norm_le F P a s ha) (by norm_num))

variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def sourceExteriorValueEuler (a : SourceExteriorPrime F S₀ → ℂ) (s : ℂ) : ℂ :=
  ∏' P, (1 - sourcePrimeEulerRatio F P.val (a P) s)⁻¹

theorem sourceExteriorValueEuler_hasProd_exp (a : SourceExteriorPrime F S₀ → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : SourceExteriorPrime F S₀ => (1 - sourcePrimeEulerRatio F P.val (a P) s)⁻¹)
      (Complex.exp (∑' P : SourceExteriorPrime F S₀, -Complex.log (1 - sourcePrimeEulerRatio F P.val (a P) s))) := by
  have hS := ((sourcePrimeNormRpow_summable F hs).comp_injective
    (i := fun P : SourceExteriorPrime F S₀ => P.val) Subtype.val_injective).mul_left (3 / 2 : ℝ)
  have hL := Summable.of_norm_bounded hS (fun P =>
    sourcePrimeEulerLog_norm_le F P.val (a P) s (ha P) hs.le)
  have H := hL.hasSum.cexp
  apply H.congr_fun
  intro P
  have hn := sourceOneSub_ne_zero_of_norm_lt_one
    ((sourcePrimeEulerRatio_norm_le_half F P.val (a P) s (ha P) hs.le).trans_lt (by norm_num))
  simp only [Function.comp_def, Complex.exp_neg, Complex.exp_log hn]

theorem sourceExteriorValueEuler_hasProd (a : SourceExteriorPrime F S₀ → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : SourceExteriorPrime F S₀ => (1 - sourcePrimeEulerRatio F P.val (a P) s)⁻¹)
      (sourceExteriorValueEuler F S₀ a s) := by
  have H := sourceExteriorValueEuler_hasProd_exp F S₀ a ha s hs
  rw [sourceExteriorValueEuler, H.tprod_eq]
  exact H

theorem sourceExteriorValueEuler_ne_zero (a : SourceExteriorPrime F S₀ → ℂ)
    (ha : ∀ P, ‖a P‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    sourceExteriorValueEuler F S₀ a s ≠ 0 := by
  rw [sourceExteriorValueEuler, (sourceExteriorValueEuler_hasProd_exp F S₀ a ha s hs).tprod_eq]
  exact Complex.exp_ne_zero _

theorem sourceExteriorValueEuler_eq_ray {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
    (s : ℂ) (hs : 1 < s.re) :
    sourceExteriorValueEuler F S₀ (fun P => η.allCoefficient P.val.asIdeal) s =
      sourceExteriorRaySeries F S₀ η s :=
  (sourceExteriorRay_hasProd F S₀ η s hs).tprod_eq

end
end ArtinMatthews.SourceEulerAssembly
