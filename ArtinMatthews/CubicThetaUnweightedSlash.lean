module

public import ArtinMatthews.CubicThetaUnweightedGenerators
public import Mathlib.NumberTheory.ModularForms.SlashActions


set_option backward.privateInPublic true
@[expose] public section

/-! Native weight-one slash identities for the two level-three generators. -/
noncomputable section
namespace ArtinMatthews

open Complex UpperHalfPlane ModularForm
open scoped MatrixGroups

/-- Actual unweighted Eisenstein theta is fixed by the translation generator. -/
theorem eisensteinHolomorphicTheta_slash_T :
    eisensteinHolomorphicTheta ∣[(1 : ℤ)] ModularGroup.T =
      eisensteinHolomorphicTheta := by
  funext τ
  rw [SL_slash_apply, UpperHalfPlane.modular_T_smul]
  have hd : UpperHalfPlane.denom ModularGroup.T τ = 1 := by
    erw [ModularGroup.denom_apply]
    norm_num [ModularGroup.T]
  rw [hd]
  simpa only [Int.cast_one, one_zpow, mul_one] using
    eisensteinHolomorphicTheta_int_translate 1 τ

/-- Actual unweighted Eisenstein theta is fixed by every lower unipotent
matrix whose parameter is divisible by three. -/
theorem eisensteinHolomorphicTheta_slash_lowerUnipotent (n : ℤ) :
    eisensteinHolomorphicTheta ∣[(1 : ℤ)] eisensteinLowerUnipotent n =
      eisensteinHolomorphicTheta := by
  funext τ
  rw [SL_slash_apply, eisensteinHolomorphicTheta_lowerUnipotent]
  have hd : UpperHalfPlane.denom (eisensteinLowerUnipotent n) τ =
      (3 * n : ℂ) * τ + 1 := by
    erw [ModularGroup.denom_apply]
    simp [eisensteinLowerUnipotent]
  have hn : (3 * n : ℂ) * τ + 1 ≠ 0 :=
    hd ▸ UpperHalfPlane.denom_ne_zero (eisensteinLowerUnipotent n) τ
  rw [hd]
  simp only [zpow_neg_one]
  field_simp [hn]

end ArtinMatthews
