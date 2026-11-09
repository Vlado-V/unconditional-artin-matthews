module

public import ArtinMatthews.SourceKPJacquetDiagonalBounds
public import ArtinMatthews.SourceKPJacquetFlatDiagonalEquiv


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit stable frequency cutoff and the invertible diagonal
transport, with the root depths chosen once for the original vector. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "a₀" => fun t : Lˣ => l₀ (sourceGL2Diagonal t)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
    (C : Submodule ℂ (sourceAlgebraicInducedSpace _ ρ))
    {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
    (hC : ∀ (g : SourceFiniteKP2Projective K hζ P) (f : sourceAlgebraicInducedSpace _ ρ),
      f ∈ C → sourceAlgebraicInducedRepresentation (SourceFiniteKPProjectiveBorel K hζ P) ρ g f ∈ C)
    (hUpper : ∀ t : P.adicCompletion K, ∀ v : V,
      ρ (sourceFiniteKPProjectiveBorelUpper K hζ P t) v = v)
    (hCube : SourceKPJacquetNegativeCubeLaw K hζ P ρ)
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C)
local notation "r₀" => sourceKPJacquetRight K hζ P ρ C hC
local notation "hU" => sourceKPJacquet_unitCube_of_negativeCubeLaw K hζ P ρ hCube
local notation "J" => sourceKPJacquetStableMap K hζ P ρ C e hUpper hU hSmooth
local notation "D" => sourceKPJacquetFlatDiagonal K hζ P ρ
local notation "Fz" => sourceKPJacquetFrequencyTruncation K hζ P ρ e
local notation "R₀" => sourceKPJacquetFrequencyRadius K P

theorem sourceKPJacquetStableMap_diagonal_stabilized (f : C) :
    ∃ M N : ℕ, ∀ z : Lˣ,
      let u := Fz z (R₀ M N z : ℤ) f.val
      SourceKPJacquetFrequencyHasStableValue K hζ P ρ e z f.val u ∧
        J (r₀ (a₀ z) f) = (↑(‖(z : L)‖ ^ (2 / 3 : ℝ)) : ℂ) •
          sourceKPJacquetFlatDiagonalEquiv K hζ P ρ z⁻¹ u := by
  obtain ⟨N, hFix⟩ := hSmooth f
  obtain ⟨M, _, hTiny⟩ := sourceKPJacquet_tiny_unit_cube K P
  refine ⟨M, N, fun z => ⟨?_, ?_⟩⟩
  · exact sourceKPJacquetFrequencyHasStableValue_cutoff K hζ P ρ hUpper hU e f.val M N hTiny hFix z
  · let u := Fz z (R₀ M N z : ℤ) f.val
    let c : ℂ := ↑(‖(z : L)‖ ^ (2 / 3 : ℝ))
    calc
      _ = c • D z⁻¹ u :=
        sourceKPJacquetStableMap_diagonal_cutoff K hζ P ρ C e hC hUpper hCube hSmooth f M N hTiny hFix z
      _ = _ := congrArg (fun x : V => c • x)
        (sourceKPJacquetFlatDiagonalEquiv_apply K hζ P ρ z⁻¹ u).symm

end
end ArtinMatthews
