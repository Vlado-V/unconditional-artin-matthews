module

public import ArtinMatthews.SourceReflectionLiteralMoment
public import ArtinMatthews.SourcePoissonLogRowsExterior
public import ArtinMatthews.SourcePoissonAngularOfReflected


set_option backward.privateInPublic true
@[expose] public section

/-! Specialize Section 04 to the actual shared nonzero Poisson row set.
The two remaining analytic inputs are the genuine reflected expansion
and the quadratic large sieve for the actual exterior symbols. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic QuadraticWeil
open Filter
open scoped NumberField Classical BigOperators Topology
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)

local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "Rows" => SourceNonzeroFrequency F S₀
local notation "Classes" => ExteriorUnitSixthClasses S

theorem sourcePoissonReflectedSecondMoment_of_expansion {U : Type} [Fintype U]
    (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A)
    (hsieve : SourceReflectionQuadraticSieve F S₀ hζ) :
    SourcePoissonReflectedSecondMoment F S₀ hζ η hBad := by
  obtain ⟨K, hK, L, hb⟩ := sourcePoissonLogRows_exteriorData F S₀ hζ
  obtain ⟨C, hC, hc⟩ := exists_sourceReflectionLiteralMoment_le F S₀ hζ η hBad A hA hsieve
    hK (by norm_num : (1 : ℝ) ≤ 1033 / 1000) (by norm_num : (0 : ℝ) < 1 / 50000)
  refine ⟨C * (L : ℝ), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Z hZ₁
  intro hZ
  let X := Z ^ (9 / 10 : ℝ)
  let Y := Z ^ (133 / 1000 : ℝ)
  have hX : 0 < X := Real.rpow_pos_of_pos hZ _
  have hY : 0 < Y := Real.rpow_pos_of_pos hZ _
  let P := sourcePoissonPhysicalNonzeroRows F S₀ hζ hX hY
  let j : P ↪ Rows :=
    ⟨fun m => ⟨m.val, ((sourcePoissonPhysicalNonzeroRows_mem F S₀ hζ hX hY m.val).mp m.property).1⟩,
      fun _ _ h => Subtype.ext (congrArg (fun m : Rows => m.val) h)⟩
  let T := Finset.univ.map j
  have hT (m : Rows) (hm : m ∈ T) :
      m.val ∈ sourceScaledLatticeRows F S₀ hζ (sourcePoissonLogRowBox F S₀ hζ) (X * Y) := by
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hm
    exact ((sourcePoissonPhysicalNonzeroRows_mem F S₀ hζ hX hY x.val).mp x.property).2
  have hn : X * Y = Z ^ (1033 / 1000 : ℝ) := by
    dsimp [X, Y]
    rw [← Real.rpow_add hZ]
    norm_num
  have hdata := hb (X * Y) (mul_pos hX hY)
  have hm := hc Z hZ₁ T L (fun m hm => by rw [← hn]; exact hdata.1 m (hT m hm)) (hdata.2 T hT)
  have he : (2 * (1033 / 1000 : ℝ) - 1 + 1 / 50000) = 533 / 500 + 1 / 50000 := by norm_num
  rw [he] at hm
  change (∑ m ∈ P, ‖reflectionCoefficientRow F hζ S₀ hBad η m Z‖ ^ 2) ≤
    C * (L : ℝ) * Z ^ (533 / 500 + 1 / 50000 : ℝ)
  refine le_trans ?_ hm
  apply le_of_eq
  symm
  dsimp only [T]
  rw [Finset.sum_map]
  exact Finset.sum_coe_sort P (fun m : R => ‖reflectionCoefficientRow F hζ S₀ hBad η m Z‖ ^ 2)

end
end ArtinMatthews.SourceEulerAssembly
