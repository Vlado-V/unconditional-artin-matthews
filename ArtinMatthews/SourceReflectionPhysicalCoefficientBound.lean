module

public import ArtinMatthews.SourceReflectionPhysicalProfiles
public import ArtinMatthews.SourceReflectionDirichletMajorant


set_option backward.privateInPublic true
@[expose] public section

/-! The actual separated physical coefficient is dominated by the
Dirichlet weight before smoothing. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators QuadraticWeil VaryingKummerAnalytic
open scoped NumberField
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)

local notation "E" => SourcePrimeExponents F S₀
local notation "Prime" => SourceExteriorPrime F S₀
local notation "S" => sourceHilbertSet F S₀
local notation "GS" => sourceReflectionExteriorGuardedSeparated F S₀ hζ hS

theorem sourceReflectionExteriorGuardedSeparated_norm_le_dirichlet
    (ε : exteriorUnitSubgroup S) (h d : E) (f : Finset Prime)
    (i : SourceReflectionTermIndex F S₀ f) :
    ‖GS ε h f i.1.val i.2.1 d i.2.2.val‖ ≤ sourceReflectionDirichletTerm F S₀ f 0 i := by
  let a := i.1.val
  let n := i.2.1
  let c := i.2.2.val
  let b := sourceReflectionExteriorGuardedFrozen F S₀ hζ hS ε h f a n
  let r := sourceReflectionExteriorGuardedRow F S₀ hζ hS ε h f a n d
  let t := sourceReflectionExteriorColumn F S₀ hζ ε h f a c
  let q := sourceReflectionQuadraticSymbol F S₀ hζ d c
  let Nc : ℝ := sourcePrimeExponentNorm F S₀ c
  let Nn := sourcePrimeExponentNorm F S₀ n
  have hb := sourceReflectionExteriorGuardedFrozen_norm_le F S₀ hζ hS ε h f a n
  have hr := sourceReflectionExteriorGuardedRow_norm_le_one F S₀ hζ hS ε h f a n d
  have ht := sourceReflectionExteriorColumn_norm_le_one F S₀ hζ hS ε h f a c
  have hq := sourceReflectionQuadraticSymbol_norm_le_one F S₀ hζ d c
  rw [sourceReflectionDirichletTerm_zero]
  change ‖b * r * t * q / ((Real.sqrt Nc : ℂ) * (Nn : ℂ))‖ ≤
    sourceReflectionFrozenWeight F S₀ f a / (Real.sqrt Nc * (Nn : ℝ))
  rw [norm_div, norm_mul ((Real.sqrt Nc : ℂ)), Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
  rw [norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ ‖b‖ * ‖r‖ * ‖t‖ := mul_le_of_le_one_right (by positivity) hq
    _ ≤ ‖b‖ * ‖r‖ := mul_le_of_le_one_right (by positivity) ht
    _ ≤ ‖b‖ := mul_le_of_le_one_right (norm_nonneg _) hr
    _ ≤ _ := hb

variable [IsTotallyComplex F] {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)

theorem sourceReflectionPhysicalCoefficient_norm_le_dirichlet
    (u ε : exteriorUnitSubgroup S) (h d : E) (f : Finset Prime)
    (i : SourceReflectionTermIndex F S₀ f) {κ : ℂ} (hκ : ‖κ‖ ≤ 1) :
    ‖GS ε h f i.1.val i.2.1 d i.2.2.val *
      (sourceKPPhysicalNegativeScalarPhase F hζ S₀ hS η hJ u ε f i.1.val i.2.1 *
        sourceKPPhysicalNegativeRowPhase F hζ S₀ hS η hJ u d *
        sourceKPPhysicalNegativeColumnPhase F hζ S₀ hS η hJ u i.2.2.val) * κ‖ ≤
      sourceReflectionDirichletTerm F S₀ f 0 i := by
  simp only [norm_mul, sourceKPPhysicalNegativeScalarPhase_norm,
    sourceKPPhysicalNegativeRowPhase_norm, sourceKPPhysicalNegativeColumnPhase_norm, mul_one]
  exact (mul_le_of_le_one_right (norm_nonneg _) hκ).trans
    (sourceReflectionExteriorGuardedSeparated_norm_le_dirichlet F S₀ hζ hS ε h d f i)

end
end ArtinMatthews.SourceEulerAssembly
