module

public import ArtinMatthews.MarkedRootMemoryEndpointTest
public import ArtinMatthews.MarkedMemoryOrderedIndicatorTests
public import ArtinMatthews.MarkedPhysicalMemoryHistoryIndex
public import ArtinMatthews.MarkedPhysicalIndexRootGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! Integrate the actual ordered endpoint tests of a chronological
history. The result is the literal good volume of its original physical
coordinate index, with normalized measure mass fifteen unchanged. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (e : J → ℝ) (x d₀ Y U V : ℝ) {B R n : ℕ}
  (hZ : ∀ z ∈ markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  {s : MarkedRawState (markedRawActualPrimeBand e x) (⌊(Real.log x)^(1/100:ℝ)⌋₊+1) B
    (markedPrimitiveCoordinateTube R)}
  (H : MarkedMemoryChronologicalHistory hZ n s)

def markedPhysicalActualIndexActive
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (v : Fin (n+1)) : MarkedRawActive (markedRawActualPrimeBand e x) (⌊(Real.log x)^(1/100:ℝ)⌋₊+1) :=
  markedPhysicalCoordinateIndexRawActive (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) ⌊(Real.log x)^(1/100:ℝ)⌋₊ i v

def markedPhysicalMemoryHistoryActualIndex :
    MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R :=
  markedPhysicalMemoryHistoryIndex (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hZ H

omit [DecidableEq J] in
theorem markedPhysicalMemoryHistoryActualIndex_path (hs : s.1.1=(1,0)) (v : Fin (n+1)) :
    markedPhysicalCoordinateIndexPath (markedPhysicalMemoryHistoryActualIndex e x hZ H).2.1 v=
      (markedMemoryHistoryVertexState hZ H v).1.1 :=
  markedPhysicalMemoryHistoryIndex_path _ _ hZ H hs v

omit [DecidableEq J] in
theorem markedPhysicalMemoryHistoryIndex_raw_active (v : Fin (n+1)) :
    markedPhysicalActualIndexActive e x (markedPhysicalMemoryHistoryActualIndex e x hZ H) v=
      (markedMemoryHistoryVertexState hZ H v).2.1 := by
  exact Equiv.symm_apply_apply _ _

theorem markedPhysicalHistoryEndpointGood_iff (hs : s.1.1=(1,0)) (hR : 1≤R)
    (p : ℝ × (ℝ × ℝ)) :
    (∀ v : Fin (n+1),MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p
      (markedMemoryHistoryVertexState hZ H v)) ↔
      p ∈ markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V
        (markedPhysicalMemoryHistoryActualIndex e x hZ H) hR := by
  let i := markedPhysicalMemoryHistoryActualIndex e x hZ H
  have hz (v : Fin (n+1)) : markedPhysicalCoordinateIndexPath i.2.1 v=
      (markedMemoryHistoryVertexState hZ H v).1.1 :=
    markedPhysicalMemoryHistoryActualIndex_path e x hZ H hs v
  change (∀ v,MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p
      (markedMemoryHistoryVertexState hZ H v)) ↔
    p ∈ markedRootGoodPathSet e x Finset.univ
      (markedPhysicalActualIndexActive e x i)
      d₀ Y U V
      (fun v => markedRootIntegerVector (markedPhysicalCoordinateIndexPath i.2.1 v))
      (fun v => markedRootIntegerVector (markedPrimitiveCoordinateCompletion
        (markedPhysicalCoordinateIndexPath i.2.1 v) (markedPhysicalCoordinateIndexPath_primitive hR i.2.1 v)))
  simp only [markedRootGoodPathSet,Set.mem_inter_iff,Set.mem_ofPred_eq,
    MarkedRootPhysicalGoodPath,Finset.mem_univ,forall_const]
  simp only [hz]
  constructor
  · intro h
    refine ⟨((markedRootMemoryEndpointGood_iff e x d₀ Y U V hZ p _).mp (h 0)).1,?_⟩
    exact fun v => ((markedRootMemoryEndpointGood_iff e x d₀ Y U V hZ p _).mp (h v)).2
  · rintro ⟨hd,h⟩ v
    exact (markedRootMemoryEndpointGood_iff e x d₀ Y U V hZ p _).mpr ⟨hd,h v⟩

theorem markedPhysicalHistoryEndpointTests_eq_indicator (hs : s.1.1=(1,0)) (hR : 1≤R)
    (hn : 0<n) (orientation : ℕ → Bool) (offset : ℕ) (p : ℝ × (ℝ × ℝ)) :
    markedMemoryStageTestProduct hZ
      (fun k => if orientation k then fun u => star (markedRootMemoryEndpointTest e x d₀ Y U V hZ p u)
        else markedRootMemoryEndpointTest e x d₀ Y U V hZ p) n offset H=
      if p ∈ markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V
        (markedPhysicalMemoryHistoryActualIndex e x hZ H) hR then 1 else 0 := by
  unfold markedRootMemoryEndpointTest
  rw [markedMemoryStageTestProduct_oriented_indicator hZ
    (MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p)
    (markedRootMemoryEndpointGood_ghost e x d₀ Y U V hZ p)
    (markedRootMemoryEndpointGood_slots e x d₀ Y U V hZ p) orientation n offset hn H]
  have he := markedPhysicalHistoryEndpointGood_iff e x d₀ Y U V hZ H hs hR p
  by_cases hp : ∀ v : Fin (n+1),MarkedRootMemoryEndpointGood e x d₀ Y U V hZ p
      (markedMemoryHistoryVertexState hZ H v)
  · rw [ite_eq_left hp,ite_eq_left (he.mp hp)]
  · rw [ite_eq_right hp,ite_eq_right (fun h => hp (he.mpr h))]

theorem markedPhysicalHistoryEndpointTests_integrable (hs : s.1.1=(1,0)) (hR : 1≤R)
    (hn : 0<n) (orientation : ℕ → Bool) (offset : ℕ) :
    Integrable (fun p => markedMemoryStageTestProduct hZ
      (fun k => if orientation k then fun u => star (markedRootMemoryEndpointTest e x d₀ Y U V hZ p u)
        else markedRootMemoryEndpointTest e x d₀ Y U V hZ p) n offset H) markedNormalizedRootMeasure := by
  simp_rw [markedPhysicalHistoryEndpointTests_eq_indicator e x d₀ Y U V hZ H hs hR hn orientation offset]
  exact markedRootConstantIndicator_integrable _
    (markedPhysicalCoordinateIndexGoodSet_measurable _ _ _ _ _ _ _ _) 1

theorem markedPhysicalHistoryEndpointTests_integral (hs : s.1.1=(1,0)) (hR : 1≤R)
    (hn : 0<n) (orientation : ℕ → Bool) (offset : ℕ) :
    (∫ p,markedMemoryStageTestProduct hZ
      (fun k => if orientation k then fun u => star (markedRootMemoryEndpointTest e x d₀ Y U V hZ p u)
        else markedRootMemoryEndpointTest e x d₀ Y U V hZ p) n offset H ∂markedNormalizedRootMeasure)=
      (markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U V
        (markedPhysicalMemoryHistoryActualIndex e x hZ H) hR:ℂ) := by
  simp_rw [markedPhysicalHistoryEndpointTests_eq_indicator e x d₀ Y U V hZ H hs hR hn orientation offset]
  rw [markedRootConstantIndicator_integral _
    (markedPhysicalCoordinateIndexGoodSet_measurable _ _ _ _ _ _ _ _),
    markedPhysicalCoordinateIndexGoodSet_volume]
  simp only [Algebra.smul_def,mul_one]
  rfl

theorem markedPhysicalHistoryEndpointTests_weighted_integrable (hs : s.1.1=(1,0)) (hR : 1≤R)
    (hn : 0<n) (orientation : ℕ → Bool) (offset : ℕ) (A F : ℂ) :
    Integrable (fun p => A*(markedMemoryStageTestProduct hZ
      (fun k => if orientation k then fun u => star (markedRootMemoryEndpointTest e x d₀ Y U V hZ p u)
        else markedRootMemoryEndpointTest e x d₀ Y U V hZ p) n offset H*F)) markedNormalizedRootMeasure :=
  ((markedPhysicalHistoryEndpointTests_integrable e x d₀ Y U V hZ H hs hR hn orientation offset).mul_const F).const_mul A

theorem markedPhysicalHistoryEndpointTests_weighted_integral (hs : s.1.1=(1,0)) (hR : 1≤R)
    (hn : 0<n) (orientation : ℕ → Bool) (offset : ℕ) (A F : ℂ) :
    (∫ p,A*(markedMemoryStageTestProduct hZ
      (fun k => if orientation k then fun u => star (markedRootMemoryEndpointTest e x d₀ Y U V hZ p u)
        else markedRootMemoryEndpointTest e x d₀ Y U V hZ p) n offset H*F) ∂markedNormalizedRootMeasure)=
      A*((markedPhysicalCoordinateIndexGoodVolume e x d₀ Y U V
        (markedPhysicalMemoryHistoryActualIndex e x hZ H) hR:ℂ)*F) := by
  rw [integral_const_mul,integral_mul_const,
    markedPhysicalHistoryEndpointTests_integral e x d₀ Y U V hZ H hs hR hn orientation offset]

end
end ArtinMatthews
