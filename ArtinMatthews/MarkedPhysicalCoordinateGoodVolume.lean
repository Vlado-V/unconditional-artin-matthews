module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexActivePath
public import ArtinMatthews.MarkedRootGoodPathReplacement


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized good-path volume on the fixed coordinate
carrier. The finite measure has total mass 15, kept explicitly. -/
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators Classical
noncomputable section

theorem markedNormalizedRootMeasure_univ : markedNormalizedRootMeasure Set.univ=15 := by
  unfold markedNormalizedRootMeasure
  rw [← Set.univ_prod_univ,Measure.prod_prod,← Set.univ_prod_univ,Measure.prod_prod]
  simp only [Measure.restrict_apply_univ,Real.volume_Icc]
  norm_num

theorem markedNormalizedRootMeasure_real_le (T : Set (ℝ × (ℝ × ℝ))) :
    0 ≤ markedNormalizedRootMeasure.real T ∧ markedNormalizedRootMeasure.real T≤15 := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  have h := ENNReal.toReal_mono (by rw [markedNormalizedRootMeasure_univ]; norm_num)
    (measure_mono (Set.subset_univ T) : markedNormalizedRootMeasure T ≤ markedNormalizedRootMeasure Set.univ)
  simpa only [Measure.real,markedNormalizedRootMeasure_univ,ENNReal.toReal_ofNat] using h

theorem markedPhysicalCoordinateIndexPath_primitive {n B : ℕ} (hB : 1≤B)
    (tail : Fin n → ↥(markedPrimitiveCoordinateTube B)) (v : Fin (n+1)) :
    IsCoprime (markedPhysicalCoordinateIndexPath tail v).1 (markedPhysicalCoordinateIndexPath tail v).2 :=
  ((markedPrimitiveCoordinateTube_mem B _).mp (markedPhysicalCoordinateIndexPath_mem hB tail v)).2.2

def markedPhysicalCoordinateIndexGoodVolume {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n B : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n B)
    (hB : 1≤B) : ℝ :=
  markedNormalizedRootMeasure.real
    (markedRootGoodPathSet e x Finset.univ
      (markedPhysicalCoordinateIndexRawActive (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) ⌊(Real.log x)^(1/100:ℝ)⌋₊ i)
      d₀ Y U V
      (fun v => markedRootIntegerVector (markedPhysicalCoordinateIndexPath i.2.1 v))
      (fun v => markedRootIntegerVector (markedPrimitiveCoordinateCompletion
        (markedPhysicalCoordinateIndexPath i.2.1 v) (markedPhysicalCoordinateIndexPath_primitive hB i.2.1 v))))

theorem markedPhysicalCoordinateIndexGoodVolume_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y U V : ℝ) {n B : ℕ}
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n B)
    (hB : 1≤B) :
    0 ≤ markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U V i hB ∧
      markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U V i hB≤15 :=
  markedNormalizedRootMeasure_real_le _

end
end ArtinMatthews
