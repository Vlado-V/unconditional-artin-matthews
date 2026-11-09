module

public import ArtinMatthews.MarkedPhysicalPathCoordinateTerm


set_option backward.privateInPublic true
@[expose] public section

/-! Finite sums commute with the literal zero extensions used in the
physical coordinate enumeration. Validity is tested before every sum. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalPositionPathExtend_sum_weights {κ : Type*} [Fintype κ]
    {Z : Finset (ℤ × ℤ)} {n : ℕ}
    (F : κ → MarkedPhysicalPositionPath Z n → ℂ) (p : Fin (n+1) → ℤ × ℤ) :
    markedPhysicalPositionPathExtend (fun pos => ∑ k,F k pos) p=
      ∑ k,markedPhysicalPositionPathExtend (F k) p := by
  by_cases h : ∀ v,p v∈Z
  · simp only [markedPhysicalPositionPathExtend,dite_eq_left h]
  · simp only [markedPhysicalPositionPathExtend,dite_eq_right h,Finset.sum_const_zero]

theorem markedPhysicalPathArrayExtend_sum_weights {κ J : Type*} [Fintype κ]
    {P : J → Finset ℕ} {M n : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : κ → (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ)
    (pos : MarkedPhysicalPositionPath Z n) (a : MarkedPhysicalLabelPath P M n) :
    markedPhysicalPathArrayExtend (fun p => ∑ k,F k p) pos a=
      ∑ k,markedPhysicalPathArrayExtend (F k) pos a := by
  by_cases h : MarkedPhysicalPathArrayValid pos a
  · simp only [markedPhysicalPathArrayExtend,dite_eq_left h]
  · simp only [markedPhysicalPathArrayExtend,dite_eq_right h,Finset.sum_const_zero]

theorem markedPhysicalPathCoordinateTerm_sum_weights {κ J : Type*}
    [Fintype κ] [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {M n : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : κ → (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ)
    (a : MarkedPhysicalLabelPath P M n)
    {S : ℕ} {A B C D : ℝ} (r : MarkedPhysicalCanonicalRoot S A B C D) (tail : Fin n → ℤ × ℤ) :
    markedPhysicalPathCoordinateTerm (fun p => ∑ k,F k p) a r tail=
      ∑ k,markedPhysicalPathCoordinateTerm (F k) a r tail := by
  unfold markedPhysicalPathCoordinateTerm
  simp_rw [markedPhysicalPathArrayExtend_sum_weights]
  exact markedPhysicalPositionPathExtend_sum_weights _ _

end
end ArtinMatthews
