module

public import ArtinMatthews.SpectralPoincareSeed
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


set_option backward.privateInPublic true
@[expose] public section

/-! Linearity of the actual locally finite arithmetic periodization. -/

noncomputable section
open Set
open scoped CompactlySupported MatrixGroups

namespace ArtinMatthews

variable (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]

theorem arithmeticPoincareSeed_add (ψ φ : C_c(UpperHalfPlane, ℂ)) :
    arithmeticPoincareSeed 𝒢 (ψ + φ) = arithmeticPoincareSeed 𝒢 ψ + arithmeticPoincareSeed 𝒢 φ := by
  ext z
  change (∑ᶠ g : 𝒢, (ψ (g • z) + φ (g • z))) =
    (∑ᶠ g : 𝒢, ψ (g • z)) + ∑ᶠ g : 𝒢, φ (g • z)
  exact finsum_add_distrib
    ((arithmetic_poincare_support_locallyFinite 𝒢 ψ).point_finite z)
    ((arithmetic_poincare_support_locallyFinite 𝒢 φ).point_finite z)

theorem arithmeticPoincareSeed_smul (c : ℂ) (ψ : C_c(UpperHalfPlane, ℂ)) :
    arithmeticPoincareSeed 𝒢 (c • ψ) = c • arithmeticPoincareSeed 𝒢 ψ := by
  ext z
  change (∑ᶠ g : 𝒢, c • ψ (g • z)) = c • ∑ᶠ g : 𝒢, ψ (g • z)
  exact (smul_finsum c (fun g : 𝒢 => ψ (g • z))).symm

/-- An actual linear map on compact seeds; no convergence premises remain. -/
def arithmeticPoincareLinear : C_c(UpperHalfPlane, ℂ) →ₗ[ℂ] C(UpperHalfPlane, ℂ) where
  toFun := arithmeticPoincareSeed 𝒢
  map_add' := arithmeticPoincareSeed_add 𝒢
  map_smul' := arithmeticPoincareSeed_smul 𝒢

end ArtinMatthews
