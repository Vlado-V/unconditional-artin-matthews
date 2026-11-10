module

public import ArtinMatthews.MarkedRootRatioCuts
public import ArtinMatthews.MarkedRootBoxFaces
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The exact Möbius level cuts have a controlled normalized grid tube.
The count is the size of the actual finite level family. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory

def markedRootCutNeighborhood (cuts : Finset ℝ) (h : ℝ) : Set ℝ :=
  ⋃ c ∈ cuts,Set.Icc (c-h) (c+h)

def markedRootRatioCutTube (z w : Fin 2 → ℝ) (levels : Finset ℝ) (h : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  markedRootCutNeighborhood (markedTransportedRatioCuts z w levels) h ×ˢ Set.univ

theorem markedRootCutNeighborhood_volume_le (cuts : Finset ℝ) {h : ℝ} (_hh : 0 ≤ h) :
    volume (markedRootCutNeighborhood cuts h) ≤ ENNReal.ofReal (2*(cuts.card : ℝ)*h) := by
  unfold markedRootCutNeighborhood
  apply (measure_biUnion_finset_le cuts (fun c => Set.Icc (c-h) (c+h))).trans_eq
  simp only [Real.volume_Icc,show ∀ c : ℝ,c+h-(c-h)=2*h by intro c; ring,
    Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ cuts.card)]
  congr 1
  ring

theorem markedRootRatioCutTube_measure_le (z w : Fin 2 → ℝ) (levels : Finset ℝ)
    {h : ℝ} (hh : 0 ≤ h) :
    markedNormalizedRootMeasure (markedRootRatioCutTube z w levels h) ≤
      ENNReal.ofReal (30*(levels.card : ℝ)*h) := by
  unfold markedNormalizedRootMeasure markedRootRatioCutTube
  rw [Measure.prod_prod]
  have hmass : ((volume.restrict (Set.Icc (1:ℝ) 16)).prod
      (volume.restrict (Set.Icc (1:ℝ) 2))) Set.univ = 15 := by
    rw [← Set.univ_prod_univ,Measure.prod_prod]
    simp only [Measure.restrict_apply_univ,Real.volume_Icc]
    norm_num
  rw [hmass]
  calc
    _ ≤ volume (markedRootCutNeighborhood (markedTransportedRatioCuts z w levels) h)*15 :=
      mul_le_mul' (Measure.restrict_apply_le _ _) le_rfl
    _ ≤ ENNReal.ofReal (2*((markedTransportedRatioCuts z w levels).card : ℝ)*h)*15 :=
      mul_le_mul' (markedRootCutNeighborhood_volume_le _ hh) le_rfl
    _ ≤ ENNReal.ofReal (2*(levels.card : ℝ)*h)*15 := by
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      have hc : ((markedTransportedRatioCuts z w levels).card : ℝ) ≤ (levels.card : ℝ) := by
        exact_mod_cast markedTransportedRatioCuts_card_le z w levels
      nlinarith
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(levels.card : ℝ)*h)]
      congr 1
      ring

theorem markedRootRatio_grid_level_mem (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) (levels : Finset ℝ) {p q : ℝ × (ℝ × ℝ)} {h : ℝ}
    (hq : markedTau q.1 z ≠ 0) (hlevel : markedTransportedRatio q.1 z w ∈ levels)
    (hpq : |p.1-q.1| ≤ h) : p ∈ markedRootRatioCutTube z w levels h := by
  refine ⟨?_,Set.mem_univ _⟩
  have hc := markedTransportedRatio_mem_cuts z w hdet levels hq hlevel
  rw [markedRootCutNeighborhood]
  refine Set.mem_iUnion.mpr ⟨q.1,Set.mem_iUnion.mpr ⟨hc,?_⟩⟩
  exact ⟨by linarith [(abs_le.mp hpq).1],by linarith [(abs_le.mp hpq).2]⟩

end ArtinMatthews
