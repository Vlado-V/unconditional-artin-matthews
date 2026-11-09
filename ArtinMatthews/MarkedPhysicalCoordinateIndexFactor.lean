module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexDamping


set_option backward.privateInPublic true
@[expose] public section

/-! Exact factorization of each zero-extended original physical copy
term. The complex factor is independent of the root; the remaining
factor retains physical validity, every good test and all q damping. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

theorem markedPhysicalCoordinateIndexTerm_factor
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (hV : ∀ j,0<V j)
    {n B : ℕ} (i : MarkedPhysicalCoordinateIndex P (pads+1) n B)
    {S : ℕ} [NeZero S] {A B' C D : ℝ} (hA : 1<A) (hC : 1<C)
    (r : MarkedPhysicalCanonicalRoot S A B' C D) :
    markedPhysicalCoordinateIndexTerm P hP V pads Z hZ ψ η d₀ Y Q q G i r=
      markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i*
        markedPhysicalCoordinateIndexDamping P pads Z q G i r := by
  unfold markedPhysicalCoordinateIndexTerm markedPhysicalCoordinateIndexDamping
    markedPhysicalPathCoordinateTerm markedPhysicalPositionPathExtend
  split_ifs with hp
  · let pos : MarkedPhysicalPositionPath Z n := fun v => ⟨_,hp v⟩
    change markedPhysicalPathArrayExtend
      (fun p => markedPhysicalMomentCopyPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G n p i.2.2) pos i.1=
      markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i*
        markedPhysicalPathArrayExtend (markedPhysicalMomentDampingPathTerm P pads Z q G n) pos i.1
    by_cases ha : MarkedPhysicalPathArrayValid pos i.1
    · rw [markedPhysicalPathArrayExtend,dite_eq_left ha,markedPhysicalPathArrayExtend,dite_eq_left ha]
      let p := markedPhysicalPathOfArrays pos i.1 ha
      by_cases hg : (p 0).1.1=(p (Fin.last n)).1.1 ∧ (∀ v,G (p v))
      · rw [markedPhysicalMomentCopyPathTerm,ite_eq_left hg,markedPhysicalMomentDampingPathTerm,ite_eq_left hg]
        have hpos (v : Fin (n+1)) : (pos v).1=
            markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
              (markedPhysicalCanonicalCompletion r) (markedPhysicalCoordinateIndexPath i.2.1 v) := by
          cases v using Fin.cases with
          | zero => simp [pos,markedPhysicalCoordinateIndexPath,markedPhysicalRootLift]
          | succ k => rfl
        have hf := markedPhysicalMomentCopies_eq_label_coordinate P hP V pads ψ η d₀ Y Q
          Z hZ hV q n pos i.1 ha i.2.2 (markedPhysicalCanonicalRootPosition r)
          (markedPhysicalCanonicalCompletion r) (markedPhysicalCoordinateIndexPath i.2.1)
          (markedPhysicalCanonicalCompletion_det hA hC r) hpos
        change _ = (∏ v : Fin n,
          (markedPhysicalEndpointDamping P (pads+1) q (pos v.castSucc).1:ℂ)*
          (markedPhysicalEndpointDamping P (pads+1) q (pos v.succ).1:ℂ))*
          markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i at hf
        exact hf.trans (mul_comm _ _)
      · rw [markedPhysicalMomentCopyPathTerm,ite_eq_right hg,
          markedPhysicalMomentDampingPathTerm,ite_eq_right hg,mul_zero]
    · simp only [markedPhysicalPathArrayExtend,dite_eq_right ha,mul_zero]
  · simp only [mul_zero]

theorem markedPhysicalCoordinateIndexTerm_norm_le_coefficient
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (hV : ∀ j,0<V j)
    (hq0 : 0≤q) (hq1 : q≤1) {n B : ℕ} (i : MarkedPhysicalCoordinateIndex P (pads+1) n B)
    {S : ℕ} [NeZero S] {A B' C D : ℝ} (hA : 1<A) (hC : 1<C)
    (r : MarkedPhysicalCanonicalRoot S A B' C D) :
    ‖markedPhysicalCoordinateIndexTerm P hP V pads Z hZ ψ η d₀ Y Q q G i r‖≤
      ‖markedPhysicalCoordinateIndexCoefficient P hP V pads ψ η d₀ Y Q i‖ := by
  rw [markedPhysicalCoordinateIndexTerm_factor P hP V pads Z hZ ψ η d₀ Y Q q G hV i hA hC r,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (markedPhysicalCoordinateIndexDamping_norm_le_one P pads Z q hq0 hq1 G i r)

end
end ArtinMatthews
