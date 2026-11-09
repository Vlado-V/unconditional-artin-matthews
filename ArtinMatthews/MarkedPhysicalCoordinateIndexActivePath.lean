module

public import ArtinMatthews.MarkedPhysicalCoordinateLabelSupport
public import ArtinMatthews.MarkedMemoryPathLineExpansion


set_option backward.privateInPublic true
@[expose] public section

/-! A nonzero actual pure-label coefficient and the literal distinct
full lists construct the independent-line active path directly on the
fixed coordinates. No supported physical root is chosen. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCoordinateIndexPath_mem {n B : ℕ} (hB : 1≤B)
    (tail : Fin n → ↥(markedPrimitiveCoordinateTube B)) (v : Fin (n+1)) :
    markedPhysicalCoordinateIndexPath tail v∈markedPrimitiveCoordinateTube B := by
  cases v using Fin.cases with
  | zero =>
      apply (markedPrimitiveCoordinateTube_mem B (1,0)).mpr
      refine ⟨?_,by simp,?_⟩
      · change |(1:ℤ)|≤(B:ℤ)
        rw [abs_one]
        exact_mod_cast hB
      · exact ⟨1,0,by norm_num⟩
  | succ k => exact (tail k).2

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ) (pads : ℕ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  {n B : ℕ} (i : MarkedPhysicalCoordinateIndex P (pads+1) n B)

def markedPhysicalCoordinateIndexRawActive (v : Fin (n+1)) :
    MarkedRawActive (fun j => markedRawPrimeBand (P j)) (pads+1) :=
  (markedPhysicalMarkingEquiv P hP (pads+1)).symm (i.1 v)

omit [Fintype J] [DecidableEq J] in
theorem markedPhysicalCoordinateIndexRawActive_distinct
    (ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v)) (v : Fin (n+1)) :
    MarkedRawActiveDistinct (markedPhysicalCoordinateIndexRawActive P hP pads i v) := by
  apply (markedPhysicalMarkingEquiv_distinct P hP (pads+1) _).mp
  simpa only [markedPhysicalCoordinateIndexRawActive,Equiv.apply_symm_apply] using ha v

theorem markedPhysicalCoordinateIndex_copy_ne_zero
    (h : markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i≠0) (v : Fin n) :
    markedPhysicalCoordinateLabelCopy P hP V pads ψ η d₀ Y Q v.val
      (i.1 v.castSucc) (i.1 v.succ) (i.2.2 v)
      (markedPhysicalCoordinateIndexPath i.2.1 v.castSucc) (markedPhysicalCoordinateIndexPath i.2.1 v.succ)≠0 := by
  change (∏ w : Fin n,markedPhysicalCoordinateLabelCopy P hP V pads ψ η d₀ Y Q w.val
    (i.1 w.castSucc) (i.1 w.succ) (i.2.2 w)
    (markedPhysicalCoordinateIndexPath i.2.1 w.castSucc) (markedPhysicalCoordinateIndexPath i.2.1 w.succ))≠0 at h
  exact (Finset.prod_ne_zero_iff.mp h) v (Finset.mem_univ v)

theorem markedPhysicalCoordinateIndex_exchange
    (ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v))
    (h : markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i≠0) (v : Fin n) :
    (∀ j,¬∃ k,markedPhysicalCoordinateIndexRawActive P hP pads i v.castSucc j k=
      markedPhysicalCoordinateIndexRawActive P hP pads i v.succ j ((i.2.2 v).2 j (Fin.last pads))) ∧
    (∀ j p,(∃ k,markedPhysicalCoordinateIndexRawActive P hP pads i v.succ j k=p) ↔
      ((∃ k,markedPhysicalCoordinateIndexRawActive P hP pads i v.castSucc j k=p) ∧
        p≠markedPhysicalCoordinateIndexRawActive P hP pads i v.castSucc j ((i.2.2 v).1 j (Fin.last pads))) ∨
      p=markedPhysicalCoordinateIndexRawActive P hP pads i v.succ j ((i.2.2 v).2 j (Fin.last pads))) :=
  markedPhysicalCoordinateLabelCopy_exchange P hP V pads ψ η d₀ Y Q v.val _ _ (ha v.castSucc)
    _ _ _ (markedPhysicalCoordinateIndex_copy_ne_zero P hP V pads ψ η d₀ Y Q i h v)

def markedPhysicalCoordinateIndexActivePath (hB : 1≤B)
    (ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v))
    (h : markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i≠0) :
    MarkedMemoryActivePathData (fun j => markedRawPrimeBand (P j)) pads (markedPrimitiveCoordinateTube B) n where
  position v := ⟨_,markedPhysicalCoordinateIndexPath_mem hB i.2.1 v⟩
  active v j :=
    { toFun := markedPhysicalCoordinateIndexRawActive P hP pads i v j
      inj' := markedPhysicalCoordinateIndexRawActive_distinct P hP pads i ha v j }
  incoming v j := markedPhysicalCoordinateIndexRawActive P hP pads i v.succ j ((i.2.2 v).2 j (Fin.last pads))
  outgoing v j := markedPhysicalCoordinateIndexRawActive P hP pads i v.castSucc j ((i.2.2 v).1 j (Fin.last pads))
  outgoing_present v j := ⟨(i.2.2 v).1 j (Fin.last pads),rfl⟩
  incoming_present v j := ⟨(i.2.2 v).2 j (Fin.last pads),rfl⟩
  incoming_not_source v j :=
    (markedPhysicalCoordinateIndex_exchange P hP V pads ψ η d₀ Y Q i ha h v).1 j
  exchange v j p :=
    (markedPhysicalCoordinateIndex_exchange P hP V pads ψ η d₀ Y Q i ha h v).2 j p

theorem markedPhysicalCoordinateIndexActivePath_initial (hB : 1≤B)
    (ha : ∀ v,MarkedPhysicalMarkingDistinct (i.1 v))
    (h : markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i≠0) :
    ((markedPhysicalCoordinateIndexActivePath P hP V pads ψ η d₀ Y Q i hB ha h).position 0).1=(1,0) := rfl

end
end ArtinMatthews
