module

public import ArtinMatthews.SourceKPJacquetDiagonalBounds
public import ArtinMatthews.SourceKPJacquetDiagonalLocallyConstant


set_option backward.privateInPublic true
@[expose] public section

/-! A scalar functional of the actual stable Jacquet translate has the
continuity, upper support and small-norm data of a finite Bessel factor. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "a₀" => fun t : Lˣ => sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal t)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
    (C : Submodule ℂ (sourceAlgebraicInducedSpace _ ρ))
    {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
    (hC : ∀ (g : SourceFiniteKP2Projective K hζ P) (f : sourceAlgebraicInducedSpace _ ρ),
      f ∈ C → sourceAlgebraicInducedRepresentation (SourceFiniteKPProjectiveBorel K hζ P) ρ g f ∈ C)
    (hUpper : ∀ t : P.adicCompletion K, ∀ v : V,
      ρ (sourceFiniteKPProjectiveBorelUpper K hζ P t) v = v)
    (hCube : SourceKPJacquetNegativeCubeLaw K hζ P ρ)
    (hDeep : C ≤ sourceKPJacquetDeepFixedSubspace K hζ P ρ)
local notation "r₀" => sourceKPJacquetRight K hζ P ρ C hC
local notation "hU" => sourceKPJacquet_unitCube_of_negativeCubeLaw K hζ P ρ hCube
local notation "hSmooth" => sourceKPJacquet_rootSmooth_of_deepFixed K hζ P ρ C hDeep
local notation "J" => sourceKPJacquetStableMap K hζ P ρ C e hUpper hU hSmooth

def sourceKPJacquetDiagonalScalarProfile (f : C) (ℓ : V →ₗ[ℂ] ℂ) (z : Lˣ) : ℂ :=
  ℓ (J (r₀ (a₀ z) f))

local notation "Profile" => sourceKPJacquetDiagonalScalarProfile K hζ P ρ C e hC hUpper hCube hDeep

theorem sourceKPJacquetDiagonalScalarProfile_data (f : C) (ℓ : V →ₗ[ℂ] ℂ) :
    Continuous (Profile f ℓ) ∧ ∃ n : ℤ, ∃ A : ℝ, 0 < A ∧
      (∀ z : Lˣ, z ∉ sourceLocalMulBall K P n → Profile f ℓ z = 0) ∧
      ∀ z : Lˣ, z ∈ sourceLocalMulBall K P 0 → ‖Profile f ℓ z‖ ≤ A * ‖(z : L)‖ ^ (1 / 3 : ℝ) := by
  refine ⟨sourceKPJacquet_right_diagonal_profile_continuous K hζ P ρ C hC f
    (hDeep f.property) (fun x => ℓ (J x)), ?_⟩
  obtain ⟨n, B, hB, hSupport, hSmall⟩ :=
    sourceKPJacquetStableMap_diagonal_bounds K hζ P ρ C e hC hUpper hCube hSmooth f
  let Lℓ : (ι → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (ℓ.comp e.symm.toLinearMap)
  have hLℓ (v : V) : Lℓ (e v) = ℓ v := by
    change ℓ (e.symm (e v)) = _
    rw [e.symm_apply_apply]
  refine ⟨n, (1 + ‖Lℓ‖) * B, mul_pos (by positivity) hB, ?_, ?_⟩
  · intro z hz
    change ℓ (J (r₀ (a₀ z) f)) = 0
    rw [hSupport z hz, map_zero]
  · intro z hz
    change ‖ℓ (J (r₀ (a₀ z) f))‖ ≤ _
    rw [← hLℓ]
    calc
      _ ≤ ‖Lℓ‖ * ‖e (J (r₀ (a₀ z) f))‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Lℓ‖ * (B * ‖(z : L)‖ ^ (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hSmall z hz) (norm_nonneg _)
      _ ≤ (1 + ‖Lℓ‖) * (B * ‖(z : L)‖ ^ (1 / 3 : ℝ)) := by gcongr; linarith
      _ = _ := by ring

end
end ArtinMatthews
