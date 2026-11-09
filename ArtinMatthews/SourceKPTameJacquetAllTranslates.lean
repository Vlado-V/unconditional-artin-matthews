module

public import ArtinMatthews.SourceKPTameJacquetSignedDiagonal
public import ArtinMatthews.SourceKPTameCentralAction


set_option backward.privateInPublic true
@[expose] public section

/-! Every translate of the actual exterior spherical vector has a
stable Jacquet integral. The torus unit rule retains the exact cubic
phase, and Iwasawa reduces general translates to the checked signed
diagonal and upper-root actions. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic AllowedGenerators QuadraticWeil VaryingKummerAnalytic
open scoped NumberField SourcePhysical MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "f₀" => sourceKPTameExteriorSphericalSection K hζ S₀ P
local notation "ρ₀" => sourceKPTameExteriorInducedRepresentation K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "ι₀" => sourceKPCentralComplex K hζ P.val
local notation "r₀" => sourceKPTameUniformizerCharacter K hζ P.val π₀
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P

theorem sourceKPTameExteriorSpherical_diagonal_unit_right (u : Lˣ) (hu : ν₀ (u : L) = 1) :
    ρ₀ (l₀ (sourceGL2Diagonal u)) f₀ = f₀ := by
  let k : SourceFiniteKP2Integral K P.val := ⟨sourceGL2Diagonal u, sourceKPIntegralMatrix_diagonal ν₀ u hu⟩
  have hk : sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k = l₀ (sourceGL2Diagonal u) :=
    congrArg (sourceFiniteKP2ProjectiveMk K hζ P.val) (sourceFiniteKP2CompactSection_diagonal K hζ P.val h₆ u hu)
  rw [← hk]
  exact sourceKPTameSphericalSection_right K hζ P.val h₆ π₀ hπ₀ k

theorem sourceKPTameExteriorSpherical_diagonal_unit_phase (j : ℤ) (u : Lˣ) (hu : ν₀ (u : L) = 1) :
    ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ j * u))) f₀ =
      χ₀ (sourceKPLocalUnitResidue K P.val u hu) ^ (2 * j) •
        ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ j))) f₀ := by
  let z := sourceFiniteKPHilbert K hζ P.val (π₀ ^ j) u ^ (2 : ℕ)
  have hz : ι₀ z = r₀ u ^ j := by
    have hp := sourceKPTameHilbert_phase K hζ P.val h₆ π₀ hπ₀ (π₀ ^ j) u
    have hv := (sourceKPValuationOrder_eq ν₀ π₀ 1).mpr hπ₀
    rw [sourceKPUnitPart_of_unit ν₀ π₀ u hu, sourceKPUnitPart_of_uniformizer_zpow ν₀ π₀ hπ₀,
      sourceKPValuationOrder_zpow, hv, mul_one, map_one r₀, one_zpow, mul_one] at hp
    exact hp
  have hp : ((ι₀ z⁻¹ : ℂˣ) : ℂ) = χ₀ (sourceKPLocalUnitResidue K P.val u hu) ^ (2 * j) := by
    rw [map_inv ι₀, hz, ← zpow_neg, Units.val_zpow_eq_zpow_val,
      sourceKPTameExteriorCharacter_residue K hζ S₀ P u hu, ← zpow_mul]
    rw [show (-2 : ℤ) * (-j) = 2 * j by ring]
  have hl : l₀ (sourceGL2Diagonal (π₀ ^ j * u)) =
      sourceFiniteKP2ProjectiveCenter K hζ P.val z⁻¹ *
        (l₀ (sourceGL2Diagonal (π₀ ^ j)) * l₀ (sourceGL2Diagonal u)) := by
    rw [sourceFiniteKP2ProjectiveLift_diagonal_mul]
    change l₀ (sourceGL2Diagonal (π₀ ^ j * u)) =
      sourceFiniteKP2ProjectiveCenter K hζ P.val z⁻¹ *
        (sourceFiniteKP2ProjectiveCenter K hζ P.val z * l₀ (sourceGL2Diagonal (π₀ ^ j * u)))
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [hl, map_mul ρ₀, Module.End.mul_apply, map_mul ρ₀, Module.End.mul_apply,
    sourceKPTameExteriorSpherical_diagonal_unit_right K hζ S₀ P u hu,
    sourceKPTameInducedRepresentation_center, hp]

theorem sourceKPTameJacquetHasStableValue_diagonal_unit
    (j : ℤ) (u : Lˣ) (hu : ν₀ (u : L) = 1) (v : ZMod 3 → ℂ)
    (hv : sourceKPTameJacquetHasStableValue K hζ S₀ P (ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ j))) f₀) v) :
    sourceKPTameJacquetHasStableValue K hζ S₀ P (ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ j * u))) f₀)
      (χ₀ (sourceKPLocalUnitResidue K P.val u hu) ^ (2 * j) • v) := by
  rw [sourceKPTameExteriorSpherical_diagonal_unit_phase K hζ S₀ P j u hu]
  exact sourceKPTameJacquetHasStableValue_smul K hζ S₀ P _ hv

theorem sourceKPTameJacquetHasStableValue_diagonal
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (y : Lˣ) :
    ∃ j, sourceKPTameJacquetHasStableValue K hζ S₀ P (ρ₀ (l₀ (sourceGL2Diagonal y)) f₀) j := by
  let e := sourceKPValuationOrder ν₀ y
  let u := sourceKPUnitPart ν₀ π₀ y
  have hy : π₀ ^ e * u = y := sourceKPUnitPart_factor ν₀ π₀ y
  have hu : ν₀ (u : L) = 1 := sourceKPUnitPart_valuation ν₀ π₀ hπ₀ y
  obtain ⟨j, hj⟩ := sourceKPTameJacquetHasStableValue_diagonal_uniformizer K hζ S₀ P hS e
  rw [← hy]
  exact ⟨_, sourceKPTameJacquetHasStableValue_diagonal_unit K hζ S₀ P e u hu j hj⟩

theorem sourceKPTameJacquetHasStableValue_spherical_translate
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (g : SourceFiniteKP2Projective K hζ P.val) :
    ∃ j, sourceKPTameJacquetHasStableValue K hζ S₀ P (ρ₀ g f₀) j := by
  obtain ⟨z, x, y, k, hg⟩ := sourceFiniteKP2Projective_Iwasawa_canonical K hζ P.val h₆ g
  obtain ⟨j, hj⟩ := sourceKPTameJacquetHasStableValue_diagonal K hζ S₀ P hS y
  have hr := sourceKPTameJacquetHasStableValue_upper K hζ S₀ P hj x
  have hrep : ρ₀ g f₀ = (ι₀ z : ℂ) • ρ₀ (l₀ (sourceGL2Upper x)) (ρ₀ (l₀ (sourceGL2Diagonal y)) f₀) := by
    rw [hg]
    simp only [map_mul ρ₀, Module.End.mul_apply, sourceKPTameSphericalSection_right K hζ P.val h₆ π₀ hπ₀ k,
      sourceKPTameInducedRepresentation_center]
  rw [hrep]
  exact ⟨(ι₀ z : ℂ) • (ψ₀ x • j), sourceKPTameJacquetHasStableValue_smul K hζ S₀ P (ι₀ z : ℂ) hr⟩

end
end ArtinMatthews
