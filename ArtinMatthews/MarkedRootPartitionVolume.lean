module

public import ArtinMatthews.MarkedRootPartitionCells
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Exact normalized Lebesgue mass of every faithful half-open cell.
Changing which cell owns an endpoint changes no archimedean mass. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory

theorem markedRootPartitionInterval_volume (N K : ℕ) (i : Fin K) (s : ℝ) :
    volume (markedRootPartitionInterval N K i s) = ENNReal.ofReal (1/(N:ℝ)) := by
  by_cases hi : i.val+1=K
  · have he : markedRootPartitionInterval N K i s =
        Set.Icc (s+(i:ℝ)/N) (s+((i:ℝ)+1)/N) := by
      ext x
      simp only [markedRootPartitionInterval,Set.mem_ofPred_eq,ite_eq_left hi,Set.mem_Icc]
    rw [he,Real.volume_Icc]
    congr 1
    ring
  · have he : markedRootPartitionInterval N K i s =
        Set.Ico (s+(i:ℝ)/N) (s+((i:ℝ)+1)/N) := by
      ext x
      simp only [markedRootPartitionInterval,Set.mem_ofPred_eq,ite_eq_right hi,Set.mem_Ico]
    rw [he,Real.volume_Ico]
    congr 1
    ring

theorem markedRootPartitionInterval_restrict_volume (N k : ℕ) (hN : 0 < N)
    (i : Fin (k*N)) (s : ℝ) :
    (volume.restrict (Set.Icc s (s+k))) (markedRootPartitionInterval N (k*N) i s) =
      ENNReal.ofReal (1/(N:ℝ)) := by
  have hsub : markedRootPartitionInterval N (k*N) i s ⊆ Set.Icc s (s+k) :=
    fun _ hx => markedRootGrid_interval_bounds N k i hN i.isLt s _
      (markedRootPartitionInterval_closed N (k*N) i s hx)
  rw [Measure.restrict_apply (markedRootPartitionInterval_measurable _ _ _ _),Set.inter_eq_left.mpr hsub]
  exact markedRootPartitionInterval_volume _ _ _ _

theorem markedRootPartitionCell_volume (N : ℕ) (hN : 0 < N) (i : MarkedRootGridIndex N) :
    markedNormalizedRootMeasure (markedRootPartitionCell N i) = (ENNReal.ofReal (1/(N:ℝ)))^3 := by
  have he : markedRootPartitionCell N i =
      (markedRootPartitionInterval N N i.1 0) ×ˢ
        ((markedRootPartitionInterval N (15*N) i.2.1 1) ×ˢ (markedRootPartitionInterval N N i.2.2 1)) := by
    ext p
    rfl
  have hr : (volume.restrict (Set.Icc (0:ℝ) 1)) (markedRootPartitionInterval N N i.1 0) =
      ENNReal.ofReal (1/(N:ℝ)) := by
    have hsub : markedRootPartitionInterval N N i.1 0 ⊆ Set.Icc (0:ℝ) 1 := by
      intro x hx
      simpa using markedRootGrid_interval_bounds N 1 i.1 hN (by simpa only [one_mul] using i.1.isLt)
        0 x (markedRootPartitionInterval_closed N N i.1 0 hx)
    rw [Measure.restrict_apply (markedRootPartitionInterval_measurable _ _ _ _),Set.inter_eq_left.mpr hsub]
    exact markedRootPartitionInterval_volume _ _ _ _
  have ha : (volume.restrict (Set.Icc (1:ℝ) 16)) (markedRootPartitionInterval N (15*N) i.2.1 1) =
      ENNReal.ofReal (1/(N:ℝ)) := by
    convert markedRootPartitionInterval_restrict_volume N 15 hN i.2.1 1 using 1; norm_num
  have hb : (volume.restrict (Set.Icc (1:ℝ) 2)) (markedRootPartitionInterval N N i.2.2 1) =
      ENNReal.ofReal (1/(N:ℝ)) := by
    have hsub : markedRootPartitionInterval N N i.2.2 1 ⊆ Set.Icc (1:ℝ) 2 := by
      intro x hx
      convert markedRootGrid_interval_bounds N 1 i.2.2 hN (by simpa only [one_mul] using i.2.2.isLt)
        1 x (markedRootPartitionInterval_closed N N i.2.2 1 hx) using 1; norm_num
    rw [Measure.restrict_apply (markedRootPartitionInterval_measurable _ _ _ _),Set.inter_eq_left.mpr hsub]
    exact markedRootPartitionInterval_volume _ _ _ _
  rw [markedNormalizedRootMeasure,he,Measure.prod_prod,Measure.prod_prod,hr,ha,hb]
  ring

theorem markedRootPartitionCell_real_volume (N : ℕ) (hN : 0 < N) (i : MarkedRootGridIndex N) :
    markedNormalizedRootMeasure.real (markedRootPartitionCell N i) = 1/(N:ℝ)^3 := by
  change (markedNormalizedRootMeasure (markedRootPartitionCell N i)).toReal = _
  rw [markedRootPartitionCell_volume N hN i,ENNReal.toReal_pow,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(N:ℝ))]
  ring

end ArtinMatthews
