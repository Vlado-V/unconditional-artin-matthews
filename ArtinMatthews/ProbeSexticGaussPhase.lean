module

public import ArtinMatthews.ProbeFiniteLocalGauss
public import OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine finite-field phase identities.  The local Lambda and G below are
defined from the actual Gauss sums; their identification with global Hecke
characters is a separate arithmetic assertion. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] [Fintype F]

theorem probeQuadraticCharacter_unique (χ ξ : MulChar F ℂ)
    (hχ : χ ≠ 1) (hξ : ξ ≠ 1) (hχ2 : χ ^ 2 = 1) (hξ2 : ξ ^ 2 = 1) : χ = ξ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hval (η : MulChar F ℂ) (hη : η ≠ 1) (hη2 : η ^ 2 = 1) : η g = -1 := by
    have hs : (η g) ^ 2 = 1 := by
      rw [← η.pow_apply_coe, hη2, MulChar.one_apply_coe]
    have hn : η g ≠ 1 := by
      intro h
      apply hη
      apply (MulChar.eq_iff hg η 1).mpr
      simpa only [MulChar.one_apply_coe] using h
    exact (sq_eq_one_iff.mp hs).resolve_left hn
  apply (MulChar.eq_iff hg χ ξ).mpr
  rw [hval χ hχ hχ2, hval ξ hξ hξ2]

theorem probeSextic_cube_quadratic (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (hchar : ringChar F ≠ 2) :
    χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ) := by
  have hn : χ ^ 3 ≠ 1 := by
    intro he
    have hd := (orderOf_dvd_iff_pow_eq_one).mpr he
    rw [hχ] at hd
    norm_num at hd
  have hnq : (quadraticChar F).ringHomComp (Int.castRingHom ℂ) ≠ 1 := by
    intro he
    apply quadraticChar_ne_one hchar
    ext x
    have ht := congrArg (fun η : MulChar F ℂ => η x) he
    rw [MulChar.ringHomComp_apply, MulChar.one_apply_coe] at ht
    change (quadraticChar F x : ℂ) = 1 at ht
    rw [MulChar.one_apply_coe]
    exact_mod_cast ht
  apply probeQuadraticCharacter_unique _ _ hn hnq
  · rw [← pow_mul, show 3 * 2 = 6 by decide,
      ← orderOf_dvd_iff_pow_eq_one, hχ]
  · exact ((quadraticChar_isQuadratic F).comp (Int.castRingHom ℂ)).sq_eq_one

def probeGaussGamma (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) : ℂ :=
  ProbeGauss.normalizedGauss (χ ^ j) ψ

def probeGaussLocalLambda (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  -(probeGaussGamma χ ψ 2) ^ 3

def probeGaussLocalG (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  (χ (4 : F))⁻¹ * probeGaussGamma χ ψ 3

def probeGaussLocalVartheta (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (η : ℂ) : ℂ :=
  star (probeGaussLocalLambda χ ψ) * star (probeGaussLocalG χ ψ) * η

theorem probeGaussGamma_norm (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj : χ ^ j ≠ 1) :
    ‖probeGaussGamma χ ψ j‖ = 1 := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast (Fintype.card_pos (α := F))
  rw [probeGaussGamma, ProbeGauss.normalizedGauss, norm_div,
    primitive_gaussSum_norm _ (primitiveOnIdeals_of_field _ hj) ψ hψ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_self (Real.sqrt_ne_zero'.mpr hq)

theorem probeSexticGauss_inverse_pair (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum (χ ^ 5) ψ = (Fintype.card F : ℂ) := by
  have hχ1 : χ ≠ 1 := by intro he; simp [he] at hχ
  have hχ6 : χ ^ 6 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have hχ5 : χ ^ 5 = χ⁻¹ := by
    apply (mul_left_inj χ).mp
    rw [inv_mul_cancel, ← pow_succ, hχ6]
  rw [hχ5, ProbeGauss.gauss_inverse_pair χ ψ hχ1 hψ, hminus, one_mul]

theorem probeSexticGauss_phase (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (hchar : ringChar F ≠ 2) :
    probeGaussGamma χ ψ 1 * probeGaussGamma χ ψ 2 =
      -(probeGaussLocalLambda χ ψ) * probeGaussLocalG χ ψ := by
  have hn (j : ℕ) (hj : 0 < j) (hj6 : j < 6) : χ ^ j ≠ 1 := by
    intro he
    have hd := (orderOf_dvd_iff_pow_eq_one).mpr he
    rw [hχ] at hd
    exact (Nat.not_le_of_gt hj6) (Nat.le_of_dvd hj hd)
  have hχ6 : χ ^ 6 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  have h4 : (4 : F) ≠ 0 := by
    have h2 := Ring.two_ne_zero hchar
    convert pow_ne_zero 2 h2 using 1
    norm_num
  have hχ4 : χ (4 : F) ≠ 0 := χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr h4)
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  have hs0 : (Real.sqrt (Fintype.card F) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (show 0 < (Fintype.card F : ℝ) by
      exact_mod_cast (Fintype.card_pos (α := F)))
  have hr := OAI.JacobiQuadratic.normalized_gauss_sextic_relation χ ψ hchar hψ
    (by simpa using hn 1 (by decide) (by decide)) (hn 2 (by decide) (by decide))
    (hn 4 (by decide) (by decide)) (probeSextic_cube_quadratic χ hχ hchar) hχ6 _ hs hs0
  have hr' : χ (4 : F) * probeGaussGamma χ ψ 1 * probeGaussGamma χ ψ 2 =
      probeGaussGamma χ ψ 3 * probeGaussGamma χ ψ 2 ^ 3 := by
    simpa only [probeGaussGamma, ProbeGauss.normalizedGauss, pow_one] using hr
  unfold probeGaussLocalLambda probeGaussLocalG
  apply (mul_left_inj' hχ4).mp
  field_simp
  linear_combination hr'

theorem probeSexticGauss_local_unitary (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (hchar : ringChar F ≠ 2) :
    ‖probeGaussLocalLambda χ ψ‖ = 1 ∧ ‖probeGaussLocalG χ ψ‖ = 1 := by
  have hn (j : ℕ) (hj : 0 < j) (hj6 : j < 6) : χ ^ j ≠ 1 := by
    intro he
    have hd := (orderOf_dvd_iff_pow_eq_one).mpr he
    rw [hχ] at hd
    exact (Nat.not_le_of_gt hj6) (Nat.le_of_dvd hj hd)
  have h4 : (4 : F) ≠ 0 := by
    have h2 := Ring.two_ne_zero hchar
    convert pow_ne_zero 2 h2 using 1
    norm_num
  have h4norm : ‖χ (4 : F)‖ = 1 := by
    have he : χ (4 : F) ^ 6 = 1 := by
      rw [← χ.pow_apply' (by decide : 6 ≠ 0),
        (orderOf_dvd_iff_pow_eq_one).mp (by rw [hχ]),
        MulChar.one_apply (isUnit_iff_ne_zero.mpr h4)]
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 6 ≠ 0)).mp
    rw [← norm_pow, he, norm_one]
  constructor
  · rw [probeGaussLocalLambda, norm_neg, norm_pow,
      probeGaussGamma_norm χ ψ hψ 2 (hn 2 (by decide) (by decide)), one_pow]
  · rw [probeGaussLocalG, norm_mul, norm_inv, h4norm, inv_one,
      probeGaussGamma_norm χ ψ hψ 3 (hn 3 (by decide) (by decide)), mul_one]

theorem probeSexticGauss_vartheta_phase (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (hchar : ringChar F ≠ 2) (η : ℂ) :
    probeGaussGamma χ ψ 1 * probeGaussGamma χ ψ 2 *
      probeGaussLocalVartheta χ ψ η = -η := by
  obtain ⟨hL, hG⟩ := probeSexticGauss_local_unitary χ hχ ψ hψ hchar
  have hLL : probeGaussLocalLambda χ ψ * star (probeGaussLocalLambda χ ψ) = 1 := by
    simpa only [← starRingEnd_apply, hL, one_pow, Complex.ofReal_one] using
      Complex.mul_conj' (probeGaussLocalLambda χ ψ)
  have hGG : probeGaussLocalG χ ψ * star (probeGaussLocalG χ ψ) = 1 := by
    simpa only [← starRingEnd_apply, hG, one_pow, Complex.ofReal_one] using
      Complex.mul_conj' (probeGaussLocalG χ ψ)
  rw [probeSexticGauss_phase χ hχ ψ hψ hchar, probeGaussLocalVartheta]
  calc
    _ = -(probeGaussLocalLambda χ ψ * star (probeGaussLocalLambda χ ψ)) *
        (probeGaussLocalG χ ψ * star (probeGaussLocalG χ ψ)) * η := by ring
    _ = -η := by rw [hLL, hGG]; ring

end

end ArtinMatthews.VaryingKummerAnalytic
