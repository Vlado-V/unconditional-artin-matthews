module

public import ArtinMatthews.SourceKPAdelicOrbitHeight
public import ArtinMatthews.SourceKPAdelicHeightCompact


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform bounds for the actual rational-orbit height over compact
adelic matrix sets, independent of the lift to the cubic cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicHeight_le_weyl_constant (g : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicHeight K hζ g ≤
      sourceKPAdelicHeightConstant K hζ (sourceKPWeylMatrix 𝔸[K]*g) := by
  have h := sourceKPAdelicHeight_translate K hζ (sourceKPWeylMatrix 𝔸[K]*g) (0 : K)
  simpa only [sourceKPAdelicOpenCellMatrix, map_zero, sourceKPUpperMatrix_zero, mul_one,
    ← mul_assoc, sourceKPWeylMatrix_square, one_mul, Height.mulHeight₁_zero, inv_one,
    one_pow] using h

theorem sourceKPAdelicOrbitHeight_bounded_on_matrices
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    ∃ B : ℝ, 0 < B ∧ ∀ g ∈ S, ∀ q : SourceKPAdelicProjective K hζ,
      sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g →
        sourceKPAdelicOrbitHeight K hζ q ≤ B := by
  obtain ⟨B₁,hB₁,h₁⟩ := sourceKPAdelicHeightConstant_bounded K hζ S hS
  have hW : IsCompact ((fun g : GL (Fin 2) 𝔸[K] => sourceKPWeylMatrix 𝔸[K]*g) '' S) :=
    hS.image (continuous_const.mul continuous_id)
  obtain ⟨B₂,_hB₂,h₂⟩ := sourceKPAdelicHeightConstant_bounded K hζ _ hW
  refine ⟨max B₁ B₂, lt_of_lt_of_le hB₁ (le_max_left _ _), ?_⟩
  intro g hg q hq
  apply (sourceKPAdelicOrbitHeight_le K hζ q g hq).trans
  apply max_le
  · exact (sourceKPAdelicHeight_le_weyl_constant K hζ g).trans
      ((h₂ _ ⟨g,hg,rfl⟩).trans (le_max_right _ _))
  · exact (h₁ g hg).trans (le_max_left _ _)

end
end ArtinMatthews
