module

public import ArtinMatthews.DavenportHasseSextic
public import Mathlib.NumberTheory.JacobiSum.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The cubic Gauss cube is determined by its Jacobi sum for every
primitive additive character. This eliminates any choice of additive
phase from the angular character comparison. -/
namespace ArtinMatthews.AngularLambda
open OAI.SevenEighths
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

theorem cubicGauss_cube_eq_card_mul_jacobi (χ : MulChar F ℂ) (hχ : orderOf χ = 3)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 3 = (Fintype.card F : ℂ) * jacobiSum χ χ := by
  have hn : χ ≠ 1 := by intro he; simp [he] at hχ
  have h3 : χ^3 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one,hχ]
  have h2 : χ*χ ≠ 1 := by
    simpa only [pow_two] using
      DavenportHasse.character_power_ne_one hχ (j := 2) (by decide) (by decide)
  have hinv : χ*χ = χ⁻¹ := by
    apply (mul_right_inj χ).mp
    rw [mul_inv_cancel]
    simpa only [pow_succ',pow_zero,mul_one] using h3
  have hm : χ (-1) = 1 := MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) h3
  have hprod := ProbeGauss.gauss_inverse_pair χ ψ hn hψ
  rw [hm,one_mul] at hprod
  have hJac := jacobiSum_mul_nontrivial h2 ψ
  rw [hinv] at hJac
  calc
    _ = (gaussSum χ ψ * gaussSum χ ψ) * gaussSum χ ψ := by ring
    _ = (gaussSum χ⁻¹ ψ * jacobiSum χ χ) * gaussSum χ ψ := by rw [hJac]
    _ = (gaussSum χ ψ * gaussSum χ⁻¹ ψ) * jacobiSum χ χ := by ring
    _ = _ := by rw [hprod]

theorem normalizedCubicGauss_cube_eq_jacobi (χ : MulChar F ℂ) (hχ : orderOf χ = 3)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ProbeGauss.normalizedGauss χ ψ ^ 3 =
      jacobiSum χ χ / (Real.sqrt (Fintype.card F : ℝ) : ℂ) := by
  have hs : (Real.sqrt (Fintype.card F : ℝ) : ℂ)^2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  have hs0 : (Real.sqrt (Fintype.card F : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Fintype.card_pos (α := F)))
  rw [ProbeGauss.normalizedGauss,div_pow,cubicGauss_cube_eq_card_mul_jacobi χ hχ ψ hψ,← hs]
  field_simp

end
end ArtinMatthews.AngularLambda
