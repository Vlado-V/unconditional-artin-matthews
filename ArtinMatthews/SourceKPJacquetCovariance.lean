module

public import ArtinMatthews.SourceKPJacquetKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The stable integral is independent of the finite coordinates and
has the literal upper-root character under right translation. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical MeasureTheory Filter
open scoped NumberField SourcePhysical Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "B" => sourceLocalBall K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "ψ₀" => localFiniteCharacter K P
local notation "μ₀" => sourceLocalSelfDual K P

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
    (C : Submodule ℂ (sourceAlgebraicInducedSpace _ ρ))
    {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
local notation "E₀" => sourceKPJacquetCoordinateIntegrand K hζ P ρ C e
local notation "Tr" => sourceKPJacquetTruncation K hζ P ρ C e

theorem sourceKPJacquetTruncation_coordinates {κ : Type*} [Fintype κ]
    (e' : V ≃ₗ[ℂ] (κ → ℂ)) (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C)
    (R : ℕ) (f : C) : Tr R f = sourceKPJacquetTruncation K hζ P ρ C e' R f := by
  let A : (ι → ℂ) →L[ℂ] (κ → ℂ) := LinearMap.toContinuousLinearMap
    (e'.toLinearMap.comp e.symm.toLinearMap)
  have hA (v : V) : A (e v) = e' v := by
    change e' (e.symm (e v)) = e' v
    rw [e.symm_apply_apply]
  have he : sourceKPJacquetCoordinateIntegrand K hζ P ρ C e' f w₀ = fun t => A (E₀ f w₀ t) := by
    funext t
    unfold sourceKPJacquetCoordinateIntegrand
    rw [map_smul, hA]
  have hi := sourceKPJacquetCoordinateIntegrand_integrableOn K hζ P ρ C e hSmooth f w₀ R
  apply e'.injective
  unfold sourceKPJacquetTruncation
  rw [e'.apply_symm_apply, he, A.integral_comp_comm hi]
  rfl

variable (hUpper : ∀ x : P.adicCompletion K, ∀ v : V,
      ρ (sourceFiniteKPProjectiveBorelUpper K hζ P x) v = v)
    (hCube : ∀ y : (P.adicCompletion K)ˣ,
      sourceLocalValuation K P (((y ^ 3 : (P.adicCompletion K)ˣ) : P.adicCompletion K)) = 1 →
      ∀ v : V, ρ (sourceFiniteKPProjectiveBorelDiagonal K hζ P (y ^ 3)) v = v)
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C)
local notation "J" => sourceKPJacquetStableMap K hζ P ρ C e hUpper hCube hSmooth

theorem sourceKPJacquetStableMap_coordinates {κ : Type*} [Fintype κ] (e' : V ≃ₗ[ℂ] (κ → ℂ)) :
    J = sourceKPJacquetStableMap K hζ P ρ C e' hUpper hCube hSmooth := by
  apply LinearMap.ext
  intro f
  apply sourceKPJacquetHasStableValue_unique K hζ P ρ C e
    (sourceKPJacquetStableMap_hasStableValue K hζ P ρ C e hUpper hCube hSmooth f)
  have h := sourceKPJacquetStableMap_hasStableValue K hζ P ρ C e' hUpper hCube hSmooth f
  unfold SourceKPJacquetHasStableValue at h ⊢
  filter_upwards [h] with R hR
  exact (sourceKPJacquetTruncation_coordinates K hζ P ρ C e e' hSmooth R f).trans hR

theorem sourceKPJacquetStableMap_upper
    (hC : ∀ (g : G) (f : sourceAlgebraicInducedSpace B₀ ρ),
      f ∈ C → sourceAlgebraicInducedRepresentation B₀ ρ g f ∈ C)
    (x : L) (f : C) : J (sourceKPJacquetRight K hζ P ρ C hC (n₀ x) f) = ψ₀ x • J f := by
  let f' := sourceKPJacquetRight K hζ P ρ C hC (n₀ x) f
  have hStable := sourceKPJacquetStableMap_hasStableValue K hζ P ρ C e hUpper hCube hSmooth f
  apply sourceKPJacquetHasStableValue_unique K hζ P ρ C e
    (sourceKPJacquetStableMap_hasStableValue K hζ P ρ C e hUpper hCube hSmooth f')
  unfold SourceKPJacquetHasStableValue at hStable ⊢
  filter_upwards [hStable, sourceJacquetBall_eventually_contains K P x] with R hR hx
  have he : E₀ f' w₀ = E₀ f (w₀ * n₀ x) := by
    funext t
    unfold sourceKPJacquetCoordinateIntegrand
    rw [sourceKPJacquetRight_eval, mul_assoc w₀, sourceFiniteKP2ProjectiveLift_upper_add,
      mul_assoc w₀, sourceFiniteKP2ProjectiveLift_upper_add, add_comm t x]
  have hI := sourceKPJacquetCoordinateIntegral_open_inside K hζ P ρ C e hSmooth f (1 : B₀) x R hx
  change (∫ t in B (R : ℤ), E₀ f (1 * w₀ * n₀ x) t ∂μ₀) = e (ρ 1 (ψ₀ x • Tr R f)) at hI
  rw [one_mul, map_one] at hI
  change e.symm (∫ t in B (R : ℤ), E₀ f' w₀ t ∂μ₀) = ψ₀ x • J f
  rw [he, hI]
  change e.symm (e (ψ₀ x • Tr R f)) = _
  rw [e.symm_apply_apply, hR]

end
end ArtinMatthews
