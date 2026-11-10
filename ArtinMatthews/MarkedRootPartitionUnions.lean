module

public import ArtinMatthews.MarkedRootPartitionCells
public import ArtinMatthews.MarkedRootPartitionVolume
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact mass of arbitrary unions of faithful cells. This accounts for
all arithmetic endpoint ownership without any overlap correction. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRootPartitionUnion (N : ℕ) (B : Finset (MarkedRootGridIndex N)) : Set (ℝ × (ℝ × ℝ)) :=
  ⋃ i ∈ B,markedRootPartitionCell N i

theorem markedRootPartitionUnion_measurable (N : ℕ) (B : Finset (MarkedRootGridIndex N)) :
    MeasurableSet (markedRootPartitionUnion N B) := by
  exact Finset.measurableSet_biUnion B (fun i _ => markedRootPartitionCell_measurable N i)

theorem markedRootPartitionUnion_real_volume (N : ℕ) (hN : 0 < N)
    (B : Finset (MarkedRootGridIndex N)) :
    markedNormalizedRootMeasure.real (markedRootPartitionUnion N B) = (B.card:ℝ)/(N:ℝ)^3 := by
  let : IsFiniteMeasure markedNormalizedRootMeasure := by
    unfold markedNormalizedRootMeasure
    infer_instance
  rw [markedRootPartitionUnion,measureReal_biUnion_finset]
  · simp only [markedRootPartitionCell_real_volume N hN,Finset.sum_const,nsmul_eq_mul]
    ring
  · intro i _ j _ hij
    exact markedRootPartitionCell_pairwise N hN hij
  · exact fun i _ => markedRootPartitionCell_measurable N i

theorem markedRootPartitionUnion_cell_mem_iff (N : ℕ) (hN : 0 < N)
    (B : Finset (MarkedRootGridIndex N)) (i : MarkedRootGridIndex N)
    (p : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootPartitionCell N i) :
    p ∈ markedRootPartitionUnion N B ↔ i ∈ B := by
  constructor
  · intro hm
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hm
    obtain ⟨hj,hp'⟩ := Set.mem_iUnion.mp hj
    exact (markedRootPartitionCell_unique N hN j i p hp' hp) ▸ hj
  · intro hi
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hp⟩⟩

end ArtinMatthews
