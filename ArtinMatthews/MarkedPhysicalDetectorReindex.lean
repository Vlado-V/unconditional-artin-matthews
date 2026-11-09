module

public import ArtinMatthews.MarkedPhysicalDetectorKernel
public import ArtinMatthews.MarkedPhysicalEdgeReindex


set_option backward.privateInPublic true
@[expose] public section

/-! Exact arbitrary-detector pairing reindex by ordered shared pads and
the two unshared label tuples. The actual state conditions remain in the
zero extension, with no supplied reindex or multiplicity assumption. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (η : ℝ → ℂ) (d₀ Y q : ℝ) (detector : ℤ → ℤ → ℤ → ℂ)
  (f g : MarkedPhysicalState P (pads+1) Z → ℂ)

def markedPhysicalDetectorPairTerm (s t : Z × MarkedPhysicalMarking P (pads+1)) : ℂ :=
  markedPhysicalStateExtend (fun ss => markedPhysicalStateExtend (fun tt =>
    markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ η d₀ Y q detector ss tt *
      star (f ss)*g tt) t) s

theorem markedPhysicalEdgeDetectorPairing_ambient :
    markedPhysicalEdgeDetectorPairing P hP V pads Z hZ η d₀ Y q detector f g=
      ∑ s,∑ t,markedPhysicalDetectorPairTerm P hP V pads Z hZ η d₀ Y q detector f g s t := by
  symm
  unfold markedPhysicalDetectorPairTerm
  have he (s : Z × MarkedPhysicalMarking P (pads+1)) :
      (∑ t : Z × MarkedPhysicalMarking P (pads+1),markedPhysicalStateExtend (fun ss =>
        markedPhysicalStateExtend (fun tt => markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ
          η d₀ Y q detector ss tt*star (f ss)*g tt) t) s)=
      markedPhysicalStateExtend (fun ss => ∑ tt,markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ
        η d₀ Y q detector ss tt*star (f ss)*g tt) s := by
    by_cases hs : MarkedPhysicalStateCondition s.1.1 s.2
    · simp only [markedPhysicalStateExtend,dite_eq_left hs]
      simpa only [markedPhysicalStateExtend] using
        (markedPhysicalStateExtend_sum (fun tt => markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ
          η d₀ Y q detector ⟨s,hs⟩ tt*star (f ⟨s,hs⟩)*g tt))
    · simp only [markedPhysicalStateExtend,dite_eq_right hs,Finset.sum_const_zero]
  simp_rw [he]
  exact markedPhysicalStateExtend_sum _

theorem markedPhysicalDetectorPairTerm_off_prefix
    (a b : MarkedPhysicalMarking P (pads+1))
    (hab : (markedPhysicalMarkingSplit pads a).1≠(markedPhysicalMarkingSplit pads b).1)
    (z w : Z) :
    markedPhysicalDetectorPairTerm P hP V pads Z hZ η d₀ Y q detector f g (z,a) (w,b)=0 := by
  unfold markedPhysicalDetectorPairTerm markedPhysicalStateExtend
  split_ifs with hs ht
  · have hp : ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z ⟨(z,a),hs⟩).2.1).1≠
        ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z ⟨(w,b),ht⟩).2.1).1 :=
      fun h => hab ((markedPhysicalStateToRaw_copied_eq_iff P hP pads Z _ _).mp h)
    simp only [markedPhysicalEdgeDetectorCoefficient,hp,ite_false,mul_zero,zero_mul]
  · rfl
  · rfl

theorem markedPhysicalEdgeDetectorPairing_union_labels :
    markedPhysicalEdgeDetectorPairing P hP V pads Z hZ η d₀ Y q detector f g=
      ∑ u : MarkedPhysicalMarking P (pads+2),∑ z : Z,∑ w : Z,
        markedPhysicalDetectorPairTerm P hP V pads Z hZ η d₀ Y q detector f g
          (z,markedPhysicalEdgeSource u) (w,markedPhysicalEdgeTarget u) := by
  let F := markedPhysicalDetectorPairTerm P hP V pads Z hZ η d₀ Y q detector f g
  have hzw (z : Z) (a : MarkedPhysicalMarking P (pads+1)) :
      (∑ w : Z,∑ b : MarkedPhysicalMarking P (pads+1),F (z,a) (w,b))=
        ∑ b : MarkedPhysicalMarking P (pads+1),∑ w : Z,F (z,a) (w,b) := Finset.sum_comm
  rw [markedPhysicalEdgeDetectorPairing_ambient]
  simp only [Fintype.sum_prod_type]
  change (∑ z : Z,∑ a,∑ w : Z,∑ b,F (z,a) (w,b))=_
  simp_rw [hzw]
  rw [Finset.sum_comm]
  have hz (a : MarkedPhysicalMarking P (pads+1)) :
      (∑ z : Z,∑ b : MarkedPhysicalMarking P (pads+1),∑ w : Z,F (z,a) (w,b))=
        ∑ b : MarkedPhysicalMarking P (pads+1),∑ z : Z,∑ w : Z,F (z,a) (w,b) := Finset.sum_comm
  simp_rw [hz]
  rw [← markedPhysical_shared_label_sum P pads (fun a b => ∑ z : Z,∑ w : Z,F (z,a) (w,b))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : (markedPhysicalMarkingSplit pads a).1=(markedPhysicalMarkingSplit pads b).1
  · rw [ite_eq_left hab]
  · rw [ite_eq_right hab]
    apply Finset.sum_eq_zero
    intro z _
    apply Finset.sum_eq_zero
    intro w _
    exact markedPhysicalDetectorPairTerm_off_prefix P hP V pads Z hZ η d₀ Y q detector f g a b hab z w

theorem markedPhysicalEdgeLabels_shared_pad_sum
    (F : MarkedPhysicalMarking P (pads+1) → MarkedPhysicalMarking P (pads+1) → ℂ) :
    (∑ u : MarkedPhysicalMarking P (pads+2),F (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u))=
      ∑ c : MarkedPhysicalMarking P pads,∑ b : (j : J) → ↥(P j),∑ a : (j : J) → ↥(P j),
        F ((markedPhysicalMarkingSplit pads).symm (c,b)) ((markedPhysicalMarkingSplit pads).symm (c,a)) := by
  classical
  rw [← Equiv.sum_comp (markedPhysicalMarkingSplit (pads+1)).symm]
  simp only [Fintype.sum_prod_type,markedPhysicalEdgeSource,markedPhysicalEdgeTarget,Equiv.apply_symm_apply]
  rw [← Equiv.sum_comp (markedPhysicalMarkingSplit pads).symm]
  simp only [Fintype.sum_prod_type,Equiv.apply_symm_apply]

theorem markedPhysicalEdgeDetectorPairing_shared_pads :
    markedPhysicalEdgeDetectorPairing P hP V pads Z hZ η d₀ Y q detector f g=
      ∑ c : MarkedPhysicalMarking P pads,∑ b : (j : J) → ↥(P j),∑ a : (j : J) → ↥(P j),
        ∑ z : Z,∑ w : Z,
          markedPhysicalDetectorPairTerm P hP V pads Z hZ η d₀ Y q detector f g
            (z,(markedPhysicalMarkingSplit pads).symm (c,b))
            (w,(markedPhysicalMarkingSplit pads).symm (c,a)) := by
  rw [markedPhysicalEdgeDetectorPairing_union_labels]
  exact markedPhysicalEdgeLabels_shared_pad_sum P pads
    (fun a b => ∑ z : Z,∑ w : Z,markedPhysicalDetectorPairTerm P hP V pads Z hZ η d₀ Y q detector f g (z,a) (w,b))

end
end ArtinMatthews
