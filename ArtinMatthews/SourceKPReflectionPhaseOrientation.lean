module

public import ArtinMatthews.SourceKPPhysicalRowCharacter
public import ArtinMatthews.SourceKPPhysicalHorizontal


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine horizontal reflection phase contributes one sign per
infinite place and the square of the oriented angular character. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AngularLambda VaryingKummerAnalytic
open AllowedGenerators SourceEulerAssembly SourcePhysical QuadraticWeil
open scoped NumberField Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "V" => InfinitePlace K

theorem sourceKPReflectionHorizontalPhase_angular (b : Kˣ) (ε : Bool) (v : V) :
    sourceKPReflectionHorizontalPhase K hζ b ε v =
      -((complexAngular (v.embedding (b : K)) ^ (if ε then (-1 : ℤ) else 1)) ^ (2 : ℕ)) := by
  let z := v.embedding (b : K)
  let B := z⁻¹
  have hz : z ≠ 0 := map_ne_zero v.embedding |>.mpr b.ne_zero
  have hB : B ≠ 0 := inv_ne_zero hz
  have hden : (Complex.normSq B : ℂ) = (‖B‖ : ℂ)^2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hratio : B^2 / (Complex.normSq B : ℂ) = (complexAngular B)^2 := by
    rw [complexAngular, div_pow, hden]
  have hinv : complexAngular B = (complexAngular z)⁻¹ :=
    map_inv₀ complexAngularHom z
  have hstar : star ((complexAngular B)^2) = (complexAngular z)^2 := by
    rw [star_pow, Complex.star_def, ← Complex.inv_eq_conj (complexAngular_norm hB), hinv, inv_inv]
  have hstarRatio : star (B^2) / (Complex.normSq B : ℂ) = (complexAngular z)^2 := by
    calc
      _ = star (B^2 / (Complex.normSq B : ℂ)) := by
        simp only [Complex.star_def, map_div₀, Complex.conj_ofReal]
      _ = _ := by rw [hratio, hstar]
  rw [sourceKPReflectionHorizontalPhase, sourceKPCuspRationalComplexUnit_val]
  change -(if ε then B^2 else star (B^2)) / (Complex.normSq B : ℂ) =
    -((complexAngular z ^ (if ε then (-1 : ℤ) else 1)) ^ (2 : ℕ))
  cases ε
  · simp only [Bool.false_eq_true, ite_false, zpow_one, neg_div, hstarRatio]
  · simp only [ite_true, zpow_neg_one, neg_div, hratio, hinv]

theorem sourceKPReflectionProductPhase_all_places (b : Kˣ) (ε : V → Bool) :
    sourceKPReflectionProductPhase K hζ b ε (sourceKPAllInfinitePlaces K) =
      (-1 : ℂ)^Fintype.card V * (sourceKPResidualArchAngular K ε b)^2 := by
  rw [sourceKPReflectionProductPhase, sourceKPAllInfinitePlaces, Finset.prod_map_toList]
  have hphase (v : V) : sourceKPReflectionHorizontalPhase K hζ b (ε v) v =
      (-1 : ℂ) * ((complexAngular (v.embedding (b : K)) ^
        (if ε v then (-1 : ℤ) else 1)) ^ (2 : ℕ)) := by
    rw [sourceKPReflectionHorizontalPhase_angular, neg_one_mul]
  simp only [hphase]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
  rfl

variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "D" => sWholeDiagonal K S
variable {J : Ideal (𝓞 K)}

theorem sourceKPPhysicalRowWholeCharacter_norm
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (x : SWholeUnits K S) :
    ‖(sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u x : ℂ)‖ = 1 := by
  rw [sourceKPPhysicalRowWholeCharacter_apply, Units.val_mul, norm_mul,
    sourceReflectionWholeThetaCharacter_norm, sourceReflectionSUnitCharacter_norm, mul_one]

theorem sourceKPReflectedFiniteArchPhase_eq_whole
    (hS : standardWeilBadPlaces K ⊆ S) (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (u : exteriorUnitSubgroup (sourceHilbertSet K S₀)) (b : Kˣ) :
    ((sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ u
      (sourceKPSLocalReflectionArgument K S b))⁻¹ : ℂˣ).val *
      sourceKPReflectionProductPhase K hζ b (sourceKPOrientedHorizontal K hζ)
        (sourceKPAllInfinitePlaces K) =
    (-1 : ℂ)^Fintype.card V * (sourceKPPhysicalRowWholeCharacter K hζ S₀ hS η hJ u (D b) : ℂ)^2 := by
  let χ := sourceKPPhysicalRowFiniteCharacter K hζ S₀ hS η hJ u
  have hχ : ((χ (sourceKPSLocalReflectionArgument K S b))⁻¹ : ℂˣ).val =
      (χ (D b) : ℂ)^2 := by
    change ((χ (D ((b⁻¹)^2)))⁻¹ : ℂˣ).val = _
    rw [map_pow D, map_inv D, map_pow χ, map_inv χ, ← inv_pow, inv_inv, Units.val_pow_eq_pow_val]
  change ((χ (sourceKPSLocalReflectionArgument K S b))⁻¹ : ℂˣ).val * _ = _
  rw [hχ, sourceKPReflectionProductPhase_all_places, sourceKPPhysicalRowWholeCharacter_diagonal]
  ring

end
end ArtinMatthews
