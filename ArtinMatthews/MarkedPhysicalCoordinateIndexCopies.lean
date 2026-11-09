module

public import ArtinMatthews.MarkedPhysicalActivePathIndex


set_option backward.privateInPublic true
@[expose] public section

/-! The actual nonzero physical copy determines its unique free copied
ordering on the derived active path. Prefix matching and last-slot
choices are obtained from the literal coordinate kernel support. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

theorem markedMemorySlotFiberOfOrder_equiv
    {A : Type*} [DecidableEq A] {pads : ℕ}
    (src dst : Fin (pads+1) ↪ A) (out inc : Fin (pads+1))
    (hr : (markedMemoryBirthBatch src).erase (src out)=(markedMemoryBirthBatch dst).erase (dst inc))
    (pair : MarkedMemorySlotPairFiber src dst out inc) :
    markedMemorySlotFiberOfOrder src dst out inc hr
      (markedMemorySlotPairFiberEquiv src dst out inc hr pair)=pair :=
  (markedMemorySlotPairFiberEquiv src dst out inc hr).symm_apply_apply pair

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ) (pads : ℕ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  {n R : ℕ} (i : MarkedPhysicalCoordinateIndex P (pads+1) n R)
  (hcoef : markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i≠0)

include hcoef in
theorem markedPhysicalCoordinateIndex_prefix (v : Fin n) (j : J) (k : Fin pads) :
    markedPhysicalCoordinateIndexRawActive P hP pads i v.castSucc j ((i.2.2 v).1 j k.castSucc)=
      markedPhysicalCoordinateIndexRawActive P hP pads i v.succ j ((i.2.2 v).2 j k.castSucc) := by
  let src := (markedPhysicalMarkingEquiv P hP (pads+1)).symm
    (fun j k => i.1 v.castSucc j ((i.2.2 v).1 j k))
  let dst := (markedPhysicalMarkingEquiv P hP (pads+1)).symm
    (fun j k => i.1 v.succ j ((i.2.2 v).2 j k))
  have hc := markedPhysicalCoordinateIndex_copy_ne_zero P hP V pads ψ η d₀ Y Q i hcoef v
  have hp : ((markedRawActiveSplit pads) src).1=((markedRawActiveSplit pads) dst).1 := by
    by_cases hv : v.val%2=0
    · apply (markedPhysicalCoordinateKernel_ne_zero_guards V pads ψ η d₀ Y Q src dst
        (markedPhysicalCoordinateIndexPath i.2.1 v.castSucc) (markedPhysicalCoordinateIndexPath i.2.1 v.succ) ?_).1
      intro hz
      dsimp only [src,dst] at hz
      exact hc (by simp only [markedPhysicalCoordinateLabelCopy,hv,ite_true,hz,mul_zero])
    · apply (markedPhysicalCoordinateKernel_ne_zero_guards V pads (markedRawEdgeAdjointCutoff ψ)
        (fun u => star (η u)) d₀ Y Q src dst
        (markedPhysicalCoordinateIndexPath i.2.1 v.castSucc) (markedPhysicalCoordinateIndexPath i.2.1 v.succ) ?_).1
      intro hz
      dsimp only [src,dst] at hz
      exact hc (by simp only [markedPhysicalCoordinateLabelCopy,hv,ite_false,hz,mul_zero])
  exact congrFun (congrFun hp j) k

variable (hR : 1≤R) (ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v))

local notation "path" => markedPhysicalCoordinateIndexActivePath P hP V pads ψ η d₀ Y Q i hR ha hcoef

theorem markedPhysicalCoordinateIndex_outgoingSlot (v : Fin n) (j : J) :
    markedMemoryPathOutgoingSlot path v j=(i.2.2 v).1 j (Fin.last pads) := by
  apply ((path).active v.castSucc j).injective
  exact markedMemoryPathOutgoingSlot_eq path v j

theorem markedPhysicalCoordinateIndex_incomingSlot (v : Fin n) (j : J) :
    markedMemoryPathIncomingSlot path v j=(i.2.2 v).2 j (Fin.last pads) := by
  apply ((path).active v.succ j).injective
  exact markedMemoryPathIncomingSlot_eq path v j

def markedPhysicalCoordinateIndexSlotFiber (v : Fin n) (j : J) :
    MarkedMemorySlotPairFiber ((path).active v.castSucc j) ((path).active v.succ j)
      (markedMemoryPathOutgoingSlot path v j) (markedMemoryPathIncomingSlot path v j) :=
  ⟨((i.2.2 v).1 j,((i.2.2 v).2 j).symm),by
    refine ⟨(markedPhysicalCoordinateIndex_outgoingSlot P hP V pads ψ η d₀ Y Q i hcoef hR ha v j).symm,?_,?_⟩
    · rw [markedPhysicalCoordinateIndex_incomingSlot P hP V pads ψ η d₀ Y Q i hcoef hR ha v j]
      exact Equiv.symm_apply_apply _ _
    · intro k
      exact markedPhysicalCoordinateIndex_prefix P hP V pads ψ η d₀ Y Q i hcoef v j k⟩

def markedPhysicalCoordinateIndexOrder : Fin n → J → Equiv.Perm (Fin pads) :=
  fun v j => markedMemorySlotPairFiberEquiv _ _ _ _ (markedMemoryPathActive_remaining path v j)
    (markedPhysicalCoordinateIndexSlotFiber P hP V pads ψ η d₀ Y Q i hcoef hR ha v j)

theorem markedPhysicalCoordinateIndexOrder_pair (v : Fin n) (j : J) :
    (markedMemoryPathSlotPair path v j
      (markedPhysicalCoordinateIndexOrder P hP V pads ψ η d₀ Y Q i hcoef hR ha v j)).1=
      ((i.2.2 v).1 j,((i.2.2 v).2 j).symm) :=
  congrArg Subtype.val (markedMemorySlotFiberOfOrder_equiv _ _ _ _ (markedMemoryPathActive_remaining path v j)
    (markedPhysicalCoordinateIndexSlotFiber P hP V pads ψ η d₀ Y Q i hcoef hR ha v j))

theorem markedPhysicalCoordinateIndexOrder_recovery :
    markedPhysicalActivePathIndex P hP path
      (markedPhysicalCoordinateIndexOrder P hP V pads ψ η d₀ Y Q i hcoef hR ha)=i := by
  apply Prod.ext
  · funext v
    exact (markedPhysicalMarkingEquiv P hP (pads+1)).apply_symm_apply (i.1 v)
  · apply Prod.ext
    · funext v
      rfl
    · funext v
      apply Prod.ext
      · funext j
        exact congrArg Prod.fst
          (markedPhysicalCoordinateIndexOrder_pair P hP V pads ψ η d₀ Y Q i hcoef hR ha v j)
      · funext j
        have hh := congrArg Prod.snd
          (markedPhysicalCoordinateIndexOrder_pair P hP V pads ψ η d₀ Y Q i hcoef hR ha v j)
        change (markedMemoryPathSlotPair path v j
          (markedPhysicalCoordinateIndexOrder P hP V pads ψ η d₀ Y Q i hcoef hR ha v j)).1.2.symm=
          (i.2.2 v).2 j
        simpa only [Equiv.symm_symm] using congrArg Equiv.symm hh

end
end ArtinMatthews
