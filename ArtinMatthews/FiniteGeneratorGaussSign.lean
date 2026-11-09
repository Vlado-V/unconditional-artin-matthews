module

public import ArtinMatthews.FiniteQuadraticGaussPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact sign when the standard local residue phase ψ(x/u) is replaced
by the source phase ψ(-x/u). The factor at -1 is retained explicitly. -/

namespace ArtinMatthews.QuadraticWeil

open ArtinMatthews.QuadraticGauss ArtinMatthews.VaryingKummerAnalytic
open scoped Classical
noncomputable section

variable (F : Type) [Field F] [Fintype F]

theorem positiveSquareSum_eq_negativeSexticGamma (hF : ringChar F ≠ 2)
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    (∑ x : F, ψ (x ^ 2)) / (Real.sqrt (Fintype.card F) : ℂ) =
      residueCharacter F (-1) * probeGaussGamma χ (ψ.mulShift (-1)) 3 := by
  have hminus : ψ.mulShift (-1) ≠ 1 :=
    (AddChar.mulShift_unit_eq_one_iff ψ (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))).not.mpr hψ
  have h := residueIndex_scaled hF (ψ.mulShift (-1)) hminus (a := -1) (neg_ne_zero.mpr one_ne_zero)
  rw [residueIndex_eq_sexticGamma χ hχ hF] at h
  simpa only [AddChar.mulShift_apply, neg_one_mul, neg_neg] using h

theorem residueCharacter_neg_one_of_isSquare (h : IsSquare (-1 : F)) :
    residueCharacter F (-1) = 1 := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    intro he
    rw [he, zero_mul] at hr
    exact neg_ne_zero.mpr one_ne_zero hr
  rw [hr, map_mul, ← pow_two]
  exact residueCharacter_sq hr0

omit [Fintype F] in
theorem sexticCharacter_neg_one_of_isSquare (χ : MulChar F ℂ) (hχ : orderOf χ = 6)
    (h : IsSquare (-1 : F)) : χ (-1) = 1 := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    intro he
    rw [he, zero_mul] at hr
    exact neg_ne_zero.mpr one_ne_zero hr
  have hr2 : r ^ 2 = -1 := by simpa only [pow_two] using hr.symm
  have hr4 : r ^ 4 = 1 := by
    calc
      _ = (r ^ 2) ^ 2 := pow_mul r 2 2
      _ = 1 := by rw [hr2]; norm_num
  have h4 : χ r ^ 4 = 1 := by rw [← map_pow, hr4, map_one]
  have hc6 : χ ^ 6 = 1 := by simpa only [hχ] using pow_orderOf_eq_one χ
  have h6 : χ r ^ 6 = 1 := by
    have he := congrArg (fun η : MulChar F ℂ => η r) hc6
    simpa only [MulChar.pow_apply' χ (by decide : (6 : ℕ) ≠ 0),
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hr0)] using he
  have h2 : χ r ^ 2 = 1 := by
    have he : χ r ^ 6 = χ r ^ 4 * χ r ^ 2 := by ring
    rw [h6, h4, one_mul] at he
    exact he.symm
  rw [hr, map_mul, ← pow_two]
  exact h2

theorem positiveSquareSum_eq_negativeSexticGamma_of_isSquare (hF : ringChar F ≠ 2)
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (h : IsSquare (-1 : F)) :
    (∑ x : F, ψ (x ^ 2)) / (Real.sqrt (Fintype.card F) : ℂ) =
      probeGaussGamma χ (ψ.mulShift (-1)) 3 := by
  rw [positiveSquareSum_eq_negativeSexticGamma F hF χ hχ ψ hψ,
    residueCharacter_neg_one_of_isSquare F h, one_mul]

end

end ArtinMatthews.QuadraticWeil
