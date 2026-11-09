module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexFactor


set_option backward.privateInPublic true
@[expose] public section

/-! The structural guards of the fixed-coordinate main term are
consequences of the original physical validity and position loop. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalRootLift_eq_root_iff (root completion z : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1) :
    markedPhysicalRootLift root completion z=root ↔ z=(1,0) := by
  constructor
  · intro h
    have hh := congrArg (markedPhysicalRootCoordinates root completion) h
    simpa only [markedPhysicalRootCoordinates_lift _ _ _ hdet,
      markedPhysicalRootCoordinates_source _ _ hdet] using hh
  · intro h
    subst z
    simp [markedPhysicalRootLift]

theorem markedPhysicalCoordinateIndexDamping_ne_zero_guards
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (pads : ℕ) (Z : Finset (ℤ × ℤ)) (q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) {n B : ℕ}
    (i : MarkedPhysicalCoordinateIndex P (pads+1) n B)
    {S : ℕ} [NeZero S] {A B' C D : ℝ} (hA : 1<A) (hC : 1<C)
    (r : MarkedPhysicalCanonicalRoot S A B' C D)
    (h : markedPhysicalCoordinateIndexDamping P pads Z q G i r≠0) :
    (∀ v,MarkedPhysicalMarkingDistinct (i.1 v)) ∧
      markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) := by
  unfold markedPhysicalCoordinateIndexDamping markedPhysicalPathCoordinateTerm markedPhysicalPositionPathExtend at h
  split_ifs at h with hp
  · let pos : MarkedPhysicalPositionPath Z n := fun v => ⟨_,hp v⟩
    change markedPhysicalPathArrayExtend (markedPhysicalMomentDampingPathTerm P pads Z q G n) pos i.1≠0 at h
    unfold markedPhysicalPathArrayExtend at h
    split_ifs at h with ha
    · let p := markedPhysicalPathOfArrays pos i.1 ha
      change markedPhysicalMomentDampingPathTerm P pads Z q G n p≠0 at h
      unfold markedPhysicalMomentDampingPathTerm at h
      split_ifs at h with hg
      · refine ⟨fun v => (ha v).2.1,?_⟩
        have hh := congrArg (fun z : Z => z.1) hg.1
        apply (markedPhysicalRootLift_eq_root_iff _ _ _ (markedPhysicalCanonicalCompletion_det hA hC r)).mp
        cases n with
        | zero => simp [markedPhysicalCoordinateIndexPath,markedPhysicalRootLift]
        | succ n => exact hh.symm
      · exact False.elim (h rfl)
    · exact False.elim (h rfl)
  · exact False.elim (h rfl)

theorem markedPhysicalCoordinateIndexTerm_ne_zero_guards
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (hV : ∀ j,0<V j)
    {n B : ℕ} (i : MarkedPhysicalCoordinateIndex P (pads+1) n B)
    {S : ℕ} [NeZero S] {A B' C D : ℝ} (hA : 1<A) (hC : 1<C)
    (r : MarkedPhysicalCanonicalRoot S A B' C D)
    (h : markedPhysicalCoordinateIndexTerm P hP V pads Z hZ ψ η d₀ Y Q q G i r≠0) :
    (∀ v,MarkedPhysicalMarkingDistinct (i.1 v)) ∧
      markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i≠0 ∧
      markedPhysicalCoordinateIndexPath i.2.1 (Fin.last n)=(1,0) := by
  rw [markedPhysicalCoordinateIndexTerm_factor P hP V pads Z hZ ψ η d₀ Y Q q G hV i hA hC r] at h
  have hc := mul_ne_zero_iff.mp h
  have hg := markedPhysicalCoordinateIndexDamping_ne_zero_guards P pads Z q G i hA hC r hc.2
  exact ⟨hg.1,hc.1,hg.2⟩

end
end ArtinMatthews
