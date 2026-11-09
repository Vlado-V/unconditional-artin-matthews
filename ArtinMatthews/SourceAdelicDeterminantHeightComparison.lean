module

public import ArtinMatthews.SourceAdelicHeightComparison
public import ArtinMatthews.SourceKPAdelicBorelBand


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact determinant remainder has a uniform two-sided
effect on the full adelic Iwasawa height. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicHeight_determinant_compact_comparison :
    ∃ B : ℝ, 0 < B ∧ ∀ h ∈ (sourceKPDiagonalHom 𝔸[K]) '' sourceKPIdeleNormOneCompact K,
      ∀ g : GL (Fin 2) 𝔸[K],
        B⁻¹ * sourceKPAdelicHeight K hζ g ≤ sourceKPAdelicHeight K hζ (g * h) ∧
          sourceKPAdelicHeight K hζ (g * h) ≤ B * sourceKPAdelicHeight K hζ g :=
  sourceKPAdelicHeight_mul_uniform_on_compact K hζ _
    ((sourceKPIdeleNormOneCompact_isCompact K).image (sourceKPAdelicDiagonalMatrix_continuous K))

theorem sourceKPAdelicHeight_normOne_diagonal_comparison :
    ∃ B : ℝ, 0 < B ∧ ∀ d ∈ sourceKPIdeleNormOneCompact K,
      ∀ g : GL (Fin 2) 𝔸[K],
        B⁻¹ * sourceKPAdelicHeight K hζ g ≤
            sourceKPAdelicHeight K hζ (g * sourceKPDiagonalHom 𝔸[K] d) ∧
          sourceKPAdelicHeight K hζ (g * sourceKPDiagonalHom 𝔸[K] d) ≤
            B * sourceKPAdelicHeight K hζ g := by
  obtain ⟨B, hB, hbound⟩ := sourceKPAdelicHeight_determinant_compact_comparison K hζ
  exact ⟨B, hB, fun d hd g => hbound _ ⟨d, hd, rfl⟩ g⟩

end
end ArtinMatthews
