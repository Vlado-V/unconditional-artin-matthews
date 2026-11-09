module

public import ArtinMatthews.SourceAdelicSecondCountable
public import ArtinMatthews.SourceAdelicUnitPivot
public import ArtinMatthews.SourceRingSL2Haar
public import ArtinMatthews.SourceAdelicBlichfeldt


set_option backward.privateInPublic true
@[expose] public section

/-! Actual determinant-one adelic row actions preserve product additive Haar. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local instance sourceAdelicSL2Haar_measurableSpace : MeasurableSpace 𝔸[F] := borel 𝔸[F]
local instance sourceAdelicSL2Haar_borelSpace : BorelSpace 𝔸[F] := ⟨rfl⟩
local instance sourceAdelicSL2Haar_sFinite : SFinite (sourceKPAdelicStandardHaar F) := by
  unfold sourceKPAdelicStandardHaar
  infer_instance

def sourceSL2AdelicRowAction (g : SL(2, 𝔸[F])) : (𝔸[F] × 𝔸[F]) → (𝔸[F] × 𝔸[F]) :=
  sourceMatrixPairAction (Matrix.SpecialLinearGroup.transpose g).val

theorem sourceSL2Adelic_column_measurePreserving (g : SL(2, 𝔸[F])) :
    MeasurePreserving (sourceMatrixPairAction g.val) (sourceKPAdelicRowHaar F)
      (sourceKPAdelicRowHaar F) := by
  obtain ⟨u, hu⟩ := sourceAdelicPivotShear_isUnit F g
  exact sourceSL2_measurePreserving_of_unit_pivot (sourceKPAdelicStandardHaar F)
    g.val g.property (sourceAdelicPivotShear F g) u hu.symm

theorem sourceSL2Adelic_row_measurePreserving (g : SL(2, 𝔸[F])) :
    MeasurePreserving (sourceSL2AdelicRowAction F g) (sourceKPAdelicRowHaar F)
      (sourceKPAdelicRowHaar F) :=
  sourceSL2Adelic_column_measurePreserving F (Matrix.SpecialLinearGroup.transpose g)

theorem sourceSL2AdelicRowAction_sub (g : SL(2, 𝔸[F])) (x y : 𝔸[F] × 𝔸[F]) :
    sourceSL2AdelicRowAction F g (x - y) =
      sourceSL2AdelicRowAction F g x - sourceSL2AdelicRowAction F g y := by
  apply Prod.ext <;> simp only [sourceSL2AdelicRowAction, sourceMatrixPairAction,
    Prod.fst_sub, Prod.snd_sub] <;> ring

theorem sourceSL2AdelicRowAction_rational (g : SL(2, 𝔸[F])) (q : F × F) :
    sourceSL2AdelicRowAction F g
        (algebraMap F 𝔸[F] q.1, algebraMap F 𝔸[F] q.2) =
      (algebraMap F 𝔸[F] q.1 * g 0 0 + algebraMap F 𝔸[F] q.2 * g 1 0,
        algebraMap F 𝔸[F] q.1 * g 0 1 + algebraMap F 𝔸[F] q.2 * g 1 1) := by
  apply Prod.ext <;> simp [sourceSL2AdelicRowAction, sourceMatrixPairAction,
    Matrix.SpecialLinearGroup.transpose, mul_comm]

end
end ArtinMatthews
