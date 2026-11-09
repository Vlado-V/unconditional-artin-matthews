module

public import ArtinMatthews.ProbeSexticGaussPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Actual quadratic residue-field Gauss factors.  These definitions use the
finite sum and its positive-real normalization.  No comparison with an analytic
local Weil index or global product formula is assumed here. -/

namespace ArtinMatthews.QuadraticGauss

open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open scoped BigOperators Classical

noncomputable section

variable (F : Type*) [Field F] [Fintype F]

def residueCharacter : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

def residueIndex (ψ : AddChar F ℂ) : ℂ :=
  ProbeGauss.normalizedGauss (residueCharacter F) ψ

variable {F}

theorem residueCharacter_sq {a : F} (ha : a ≠ 0) :
    residueCharacter F a ^ 2 = 1 := by
  change (quadraticChar F a : ℂ) ^ 2 = 1
  exact_mod_cast quadraticChar_sq_one ha

theorem residueCharacter_ne_zero {a : F} (ha : a ≠ 0) :
    residueCharacter F a ≠ 0 := by
  intro h
  have hs := residueCharacter_sq ha
  rw [h, zero_pow (by decide : 2 ≠ 0)] at hs
  exact zero_ne_one hs

theorem residueCharacter_inv {a : F} (ha : a ≠ 0) :
    (residueCharacter F a)⁻¹ = residueCharacter F a := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using residueCharacter_sq ha

theorem residueCharacter_nontrivial (hF : ringChar F ≠ 2) :
    residueCharacter F ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).mpr
    (quadraticChar_ne_one hF)

theorem square_sum_eq_gauss (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    (∑ x : F, ψ (x ^ 2)) = gaussSum (residueCharacter F) ψ := by
  have hcard (y : F) :
      ((Finset.univ.filter (fun x : F => x ^ 2 = y)).card : ℂ) =
        residueCharacter F y + 1 := by
    have h := quadraticChar_card_sqrts hF y
    have hs : {x : F | x ^ 2 = y}.toFinset =
        Finset.univ.filter (fun x : F => x ^ 2 = y) := by
      ext x
      simp
    rw [hs] at h
    change _ = (quadraticChar F y : ℂ) + 1
    exact_mod_cast h
  calc
    _ = ∑ y : F,
        ((Finset.univ.filter (fun x : F => x ^ 2 = y)).card : ℂ) * ψ y := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        (Finset.sum_fiberwise' Finset.univ (fun x : F => x ^ 2) (fun y => ψ y)).symm
    _ = ∑ y : F, residueCharacter F y * ψ y + ∑ y : F, ψ y := by
      simp only [hcard, add_mul, one_mul, Finset.sum_add_distrib]
    _ = _ := by rw [AddChar.sum_eq_zero_of_ne_one hψ, add_zero]; rfl

theorem square_sum_scaled (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) {a : F} (ha : a ≠ 0) :
    (∑ x : F, ψ (a * x ^ 2)) =
      residueCharacter F a * gaussSum (residueCharacter F) ψ := by
  have hshift : ψ.mulShift a ≠ 1 :=
    (AddChar.mulShift_unit_eq_one_iff ψ (isUnit_iff_ne_zero.mpr ha)).not.mpr hψ
  calc
    _ = gaussSum (residueCharacter F) (ψ.mulShift a) :=
      square_sum_eq_gauss hF (ψ.mulShift a) hshift
    _ = (residueCharacter F)⁻¹ a * gaussSum (residueCharacter F) ψ :=
      gaussSum_mulShift_eq _ _ (Units.mk0 a ha)
    _ = _ := by rw [MulChar.inv_apply_eq_inv', residueCharacter_inv ha]

theorem residueIndex_eq_square_sum (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    residueIndex F ψ =
      (∑ x : F, ψ (x ^ 2)) / (Real.sqrt (Fintype.card F) : ℂ) := by
  rw [square_sum_eq_gauss hF ψ hψ]
  rfl

theorem residueIndex_scaled (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) {a : F} (ha : a ≠ 0) :
    (∑ x : F, ψ (a * x ^ 2)) / (Real.sqrt (Fintype.card F) : ℂ) =
      residueCharacter F a * residueIndex F ψ := by
  rw [square_sum_scaled hF ψ hψ ha]
  exact mul_div_assoc _ _ _

theorem residueIndex_sq (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    residueIndex F ψ ^ 2 = residueCharacter F (-1) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  have hg := gaussSum_sq (residueCharacter_nontrivial hF)
    ((quadraticChar_isQuadratic F).comp (Int.castRingHom ℂ))
    (AddChar.IsPrimitive.of_ne_one hψ)
  rw [residueIndex, ProbeGauss.normalizedGauss, div_pow, hs, hg]
  exact mul_div_cancel_right₀ _ hq

theorem residueIndex_fourth (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    residueIndex F ψ ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by decide, pow_mul, residueIndex_sq hF ψ hψ]
  exact residueCharacter_sq (neg_ne_zero.mpr one_ne_zero)

theorem residueIndex_norm (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) : ‖residueIndex F ψ‖ = 1 := by
  have hq : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := F))
  rw [residueIndex, ProbeGauss.normalizedGauss, norm_div,
    primitive_gaussSum_norm _ (primitiveOnIdeals_of_field _ (residueCharacter_nontrivial hF))
      ψ (AddChar.IsPrimitive.of_ne_one hψ),
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_self (Real.sqrt_ne_zero'.mpr hq)

theorem residueIndex_eq_sexticGamma (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) :
    residueIndex F ψ = VaryingKummerAnalytic.probeGaussGamma χ ψ 3 := by
  unfold residueIndex VaryingKummerAnalytic.probeGaussGamma
  rw [VaryingKummerAnalytic.probeSextic_cube_quadratic χ hχ hF]
  rfl

theorem localG_eq_quadraticIndex (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) :
    VaryingKummerAnalytic.probeGaussLocalG χ ψ =
      (χ (4 : F))⁻¹ * residueIndex F ψ := by
  rw [residueIndex_eq_sexticGamma χ hχ hF ψ]
  rfl

end

end ArtinMatthews.QuadraticGauss
