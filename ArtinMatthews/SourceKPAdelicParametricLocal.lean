module

public import ArtinMatthews.SourceKPAdelicParametricCharacter
public import ArtinMatthews.StandardLocalBallDilation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual one-place uniformizer values, with the modulus half-twist explicit. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))

local notation "Q₀" => (Ideal.absNorm P.asIdeal : ℝ)

include hπ

lemma sourceKPAdelicUniformizer_norm : ‖(π : P.adicCompletion K)‖ = Q₀⁻¹ := by
  rw [sourceLocalNorm_eq_zpow K P (π : P.adicCompletion K) π.ne_zero]
  change Q₀ ^ WithZero.log (sourceKPFiniteVal K P (π : P.adicCompletion K)) = Q₀⁻¹
  rw [hπ, WithZero.log_exp, zpow_neg_one]

theorem sourceKPIdeleComplexNorm_uniformizer (s : ℂ) (k : ℤ) :
    ((sourceKPIdeleComplexNorm K s (IdeleGroup.ofAdicCompletion (𝓞 K) K P (π^k)) : ℂˣ) : ℂ) =
      Complex.exp (-s * (k : ℂ) * (Real.log Q₀ : ℂ)) := by
  rw [sourceKPIdeleComplexNorm_coe, sourceKPIdeleAbsoluteNorm_ofAdicCompletion,
    Units.val_zpow_eq_zpow_val, norm_zpow, sourceKPAdelicUniformizer_norm K P π hπ,
    Real.log_zpow, Real.log_inv, Complex.ofReal_mul, Complex.ofReal_neg]
  congr 1
  push_cast
  ring

theorem sourceKPAdelicParametricCharacter_uniformizer_cube (s : ℂ) (k : ℤ) :
    ((sourceKPAdelicParametricCharacter K hζ s
      (sourceKPAdelicCubeTorusEquiv K hζ
        (1, sourceKPIdeleCube K (IdeleGroup.ofAdicCompletion (𝓞 K) K P (π^k)))) : ℂˣ) : ℂ) =
      Complex.exp (-3 * s * (k : ℂ) * (Real.log Q₀ : ℂ)) := by
  rw [sourceKPAdelicParametricCharacter_cube_ofAdicCompletion,
    map_one, Units.val_one, one_mul, Units.val_zpow_eq_zpow_val, norm_zpow,
    sourceKPAdelicUniformizer_norm K P π hπ, Real.log_zpow, Real.log_inv,
    Complex.ofReal_mul, Complex.ofReal_neg]
  congr 1
  push_cast
  ring

theorem sourceKPAdelicParametricCharacter_uniformizer_normalized (s : ℂ) (k : ℤ) :
    ((sourceKPIdeleComplexNorm K (1/2 : ℂ)
      ((IdeleGroup.ofAdicCompletion (𝓞 K) K P (π^k))^3) : ℂˣ) : ℂ) *
      ((sourceKPAdelicParametricCharacter K hζ s
        (sourceKPAdelicCubeTorusEquiv K hζ
          (1, sourceKPIdeleCube K (IdeleGroup.ofAdicCompletion (𝓞 K) K P (π^k)))) : ℂˣ) : ℂ) =
      Complex.exp (-3 * (s+1/2) * (k : ℂ) * (Real.log Q₀ : ℂ)) := by
  let a := IdeleGroup.ofAdicCompletion (𝓞 K) K P (π^k)
  have he : ((sourceKPIdeleComplexNorm K (1/2 : ℂ) (a^3) : ℂˣ) : ℂ) *
      ((sourceKPAdelicParametricCharacter K hζ s
        (sourceKPAdelicCubeTorusEquiv K hζ (1, sourceKPIdeleCube K a)) : ℂˣ) : ℂ) =
      ((sourceKPAdelicParametricCharacter K hζ (s+1/2)
        (sourceKPAdelicCubeTorusEquiv K hζ (1, sourceKPIdeleCube K a)) : ℂˣ) : ℂ) := by
    simp only [sourceKPAdelicParametricCharacter_equiv, map_one, one_mul]
    change ((sourceKPIdeleComplexNorm K (1/2 : ℂ) (a^3) : ℂˣ) : ℂ) *
        ((sourceKPIdeleComplexNorm K s (a^3) : ℂˣ) : ℂ) =
      ((sourceKPIdeleComplexNorm K (s+1/2) (a^3) : ℂˣ) : ℂ)
    rw [add_comm s (1/2), sourceKPIdeleComplexNorm_add, Units.val_mul]
  exact he.trans (sourceKPAdelicParametricCharacter_uniformizer_cube K hζ P π hπ (s+1/2) k)

end
end ArtinMatthews
