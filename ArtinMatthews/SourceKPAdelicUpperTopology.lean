module

public import ArtinMatthews.SourceKPAdelicHeightFactor


set_option backward.privateInPublic true
@[expose] public section

/-! Continuity of the actual additive upper-root matrix coordinates.
These statements concern the base matrix group over the adele ring. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

theorem sourceKPAdelicUpperMatrix_continuous : Continuous (sourceKPUpperMatrix 𝔸[K]) := by
  have hc : Continuous (fun y : 𝔸[K] => (sourceKPUpperMatrix 𝔸[K] y : Matrix (Fin 2) (Fin 2) 𝔸[K])) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_id
    · exact continuous_const
    · exact continuous_const
  have hi (y : 𝔸[K]) : (sourceKPUpperMatrix 𝔸[K] y)⁻¹ = sourceKPUpperMatrix 𝔸[K] (-y) := by
    apply inv_eq_iff_mul_eq_one.mpr
    rw [← sourceKPUpperMatrix_add, add_neg_cancel, sourceKPUpperMatrix_zero]
  apply Units.continuous_iff.mpr
  refine ⟨hc, ?_⟩
  simpa only [hi, Function.comp_def] using hc.comp continuous_neg

theorem sourceKPAdelicUpperRight_continuous (g : GL (Fin 2) 𝔸[K]) :
    Continuous (fun y : 𝔸[K] => sourceKPUpperMatrix 𝔸[K] y*g) :=
  (sourceKPAdelicUpperMatrix_continuous K).mul continuous_const

theorem sourceKPAdelicUpperRight_isCompact (g : GL (Fin 2) 𝔸[K])
    (S : Set 𝔸[K]) (hS : IsCompact S) :
    IsCompact ((fun y : 𝔸[K] => sourceKPUpperMatrix 𝔸[K] y*g) '' S) :=
  hS.image (sourceKPAdelicUpperRight_continuous K g)

end
end ArtinMatthews
