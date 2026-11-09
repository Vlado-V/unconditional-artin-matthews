module

public import ArtinMatthews.SourceKPJacquetFlatDiagonal


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized actual diagonal is an invertible linear action. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
local notation "L" => P.adicCompletion K

def sourceKPJacquetFlatDiagonalEquiv (u : Lˣ) : V ≃ₗ[ℂ] V := by
  let b := sourceFiniteKPProjectiveBorelDiagonal K hζ P u
  let E : V ≃ₗ[ℂ] V := LinearEquiv.ofLinearMap (ρ b) (ρ b⁻¹)
    (by
      change ρ b * ρ b⁻¹ = 1
      rw [← map_mul, mul_inv_cancel, map_one])
    (by
      change ρ b⁻¹ * ρ b = 1
      rw [← map_mul, inv_mul_cancel, map_one])
  let c : ℂ := (↑(‖(u : L)‖ ^ (-(1 / 3) : ℝ)) : ℂ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr u.ne_zero) _).ne'
  exact E.trans (LinearEquiv.smulOfNeZero ℂ V c hc)

theorem sourceKPJacquetFlatDiagonalEquiv_apply (u : Lˣ) (v : V) :
    sourceKPJacquetFlatDiagonalEquiv K hζ P ρ u v = sourceKPJacquetFlatDiagonal K hζ P ρ u v := rfl

end
end ArtinMatthews
