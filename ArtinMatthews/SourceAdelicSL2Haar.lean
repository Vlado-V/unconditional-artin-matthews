module

public import ArtinMatthews.SourceRingSL2Haar
public import ArtinMatthews.SourceAdelicBlichfeldt
public import ArtinMatthews.SourceAdelicSecondCountable
public import ArtinMatthews.SourceAdelicUnitPivot
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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
