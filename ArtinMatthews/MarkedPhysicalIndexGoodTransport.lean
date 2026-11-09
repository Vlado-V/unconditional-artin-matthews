module

public import ArtinMatthews.MarkedPhysicalLiftedRootBox
public import ArtinMatthews.MarkedPhysicalSourceBad


set_option backward.privateInPublic true
@[expose] public section

/-! Literal full-box and actual first/beta-good tests agree with the
normalized good set at each canonical integer root. Every completion is
transported by the proved determinant-one invariance. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

theorem markedPhysicalCanonicalRoot_fst_ne_zero {S : ℕ} {U V : ℝ}
    (hU : 1<U) (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) :
    (markedPhysicalCanonicalRootPosition r).1≠0 := by
  have hb := (fixedURootMatrixBox_coordinate_bounds r.1 U (16*U) 0 1 V (2*V) true true r.2.1 r.2.2).1.1
  have hp : (0:ℝ)<(r.2.1.1:ℝ) := (zero_lt_one.trans hU).trans_le hb
  change r.2.1.1≠0
  exact_mod_cast hp.ne'

theorem markedPhysicalCoordinateIndexGoodSet_mem_iff
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ)
    {n R S : ℕ} [NeZero S]
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (hU : 1<U) (hV : 1<V)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) :
    markedRootNormalizedPoint U V r.2.1 ∈ markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR ↔
      ∀ v : Fin (n+1),
        markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r)
          (markedPhysicalCoordinateIndexPath i.2.1 v) ∈ markedPhysicalPrimitiveBox U (16*U) V (2*V) ∧
        MarkedRawCircleGood e x
          (markedPhysicalCoordinateIndexRawActive (fun j => markedLogPowerBand (e j) x)
            (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) ⌊(Real.log x)^(1/100:ℝ)⌋₊ i v)
          d₀ Y (markedTransportedRatio (fixedURootRatio r.2.1)
            (markedRootIntegerVector (markedPhysicalCoordinateIndexPath i.2.1 v))
            (markedRootIntegerVector (markedPrimitiveCoordinateCompletion (markedPhysicalCoordinateIndexPath i.2.1 v)
              (markedPhysicalCoordinateIndexPath_primitive hR i.2.1 v))):AddCircle (1:ℝ)) := by
  have hd := markedRootNormalizedPoint_mem_domain r.1 hU hV r.2.1 r.2.2
  have hb (v : Fin (n+1)) :
      MarkedRootPhysicalBox U V (markedRootIntegerVector (markedPhysicalCoordinateIndexPath i.2.1 v))
        (markedRootNormalizedPoint U V r.2.1) ↔
      markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r)
        (markedPhysicalCoordinateIndexPath i.2.1 v)∈markedPhysicalPrimitiveBox U (16*U) V (2*V) := by
    rw [markedPhysicalCanonicalRoot_normalized]
    exact (markedPhysicalLift_mem_box_iff _ _ _ (markedPhysicalCanonicalRoot_fst_ne_zero hU r)
      (zero_lt_one.trans hU) (zero_lt_one.trans hV) (markedPhysicalCanonicalCompletion_det hU hV r)
      (markedPhysicalCoordinateIndexPath_primitive hR i.2.1 v)).symm
  simp only [markedPhysicalCoordinateIndexGoodSet,markedRootGoodPathSet,Set.mem_inter_iff,
    hd,true_and,Set.mem_ofPred_eq,MarkedRootPhysicalGoodPath,Finset.mem_univ,forall_const,
    MarkedRootPhysicalGoodBox]
  simp_rw [hb]
  rfl

theorem markedPhysicalCoordinateIndex_good_path_iff
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x d₀ Y U V : ℝ)
    {n R S : ℕ} [NeZero S]
    (i : MarkedPhysicalCoordinateIndex (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) n R)
    (hR : 1≤R) (hU : 1<U) (hV : 1<V)
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V))
    (w : ↥(markedPhysicalPrimitiveBox U (16*U) V (2*V)) → ℤ × ℤ)
    (hw : ∀ p,markedMinorIntegerDet p.1 (w p)=1)
    (p : Fin (n+1) → MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x)
      (markedPhysicalPrimitiveBox U (16*U) V (2*V)))
    (hpos : ∀ v,(p v).1.1.1=markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
      (markedPhysicalCanonicalCompletion r) (markedPhysicalCoordinateIndexPath i.2.1 v))
    (hlab : ∀ v,(p v).1.2=i.1 v) :
    (∀ v,MarkedPhysicalActualGood e x d₀ Y w (p v)) ↔
      markedRootNormalizedPoint U V r.2.1∈markedPhysicalCoordinateIndexGoodSet e x d₀ Y U V i hR := by
  have hg (v : Fin (n+1)) := markedRawDirtyGood_root_lift e x d₀ Y w
    (markedPhysicalStateToRaw (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x) _ (p v))
    (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r)
    (markedPhysicalCoordinateIndexPath i.2.1 v)
    (markedPrimitiveCoordinateCompletion (markedPhysicalCoordinateIndexPath i.2.1 v)
      (markedPhysicalCoordinateIndexPath_primitive hR i.2.1 v))
    (markedPhysicalCanonicalRoot_fst_ne_zero hU r) (markedPhysicalCanonicalCompletion_det hU hV r)
    (markedPrimitiveCoordinateCompletion_det _ _) (hpos v) (hw (p v).1.1)
  have hg' (v : Fin (n+1)) : MarkedPhysicalActualGood e x d₀ Y w (p v) ↔
      MarkedRawCircleGood e x
        (markedPhysicalCoordinateIndexRawActive (fun j => markedLogPowerBand (e j) x)
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) ⌊(Real.log x)^(1/100:ℝ)⌋₊ i v)
        d₀ Y (markedTransportedRatio (fixedURootRatio r.2.1)
          (markedRootIntegerVector (markedPhysicalCoordinateIndexPath i.2.1 v))
          (markedRootIntegerVector (markedPrimitiveCoordinateCompletion (markedPhysicalCoordinateIndexPath i.2.1 v)
            (markedPhysicalCoordinateIndexPath_primitive hR i.2.1 v))):AddCircle (1:ℝ)) := by
    have ha : (markedPhysicalStateToRaw (fun j => markedLogPowerBand (e j) x)
        (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) (markedPadSlots x) _ (p v)).2.1 =
        markedPhysicalCoordinateIndexRawActive (fun j => markedLogPowerBand (e j) x)
          (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) ⌊(Real.log x)^(1/100:ℝ)⌋₊ i v := by
      change (markedPhysicalMarkingEquiv _ _ (markedPadSlots x)).symm (p v).1.2 = _
      rw [hlab v]
      rfl
    have hr : ((markedPhysicalCanonicalCompletion r).1:ℝ)/(markedPhysicalCanonicalRootPosition r).1 =
        fixedURootRatio r.2.1 := rfl
    constructor
    · intro hh
      have ht := (hg v).mp hh
      rw [ha,hr] at ht
      simpa only [markedPadSlots] using ht
    · intro hh
      apply (hg v).mpr
      rw [ha,hr]
      simpa only [markedPadSlots] using hh
  rw [markedPhysicalCoordinateIndexGoodSet_mem_iff e x d₀ Y U V i hR hU hV r]
  constructor
  · intro h v
    refine ⟨?_,(hg' v).mp (h v)⟩
    rw [← hpos v]
    exact (p v).1.1.2
  · intro h v
    exact (hg' v).mpr (h v).2

end ArtinMatthews
