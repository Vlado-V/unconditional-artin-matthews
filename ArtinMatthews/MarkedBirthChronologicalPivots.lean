module

public import ArtinMatthews.MarkedBirthCyclePivots


set_option backward.privateInPublic true
@[expose] public section

/-! The cycle minimum is an earlier performed equal-value pivot for
every nonpivot. Conversely, these literal equality constraints on moved
addresses recover the actual permutation event. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A P : Type*} [Fintype A] [DecidableEq A] [LinearOrder A] (σ : Equiv.Perm A)

def markedBirthChronologicalPivot (a : A) : A :=
  if ha : a∈σ.support then
    markedBirthCyclePivot σ ⟨σ.cycleOf a,Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr ha⟩
  else a

theorem markedBirthChronologicalPivot_of_cycle
    (c : σ.cycleFactorsFinset) (a : A) (ha : a∈c.1.support) :
    markedBirthChronologicalPivot σ a=markedBirthCyclePivot σ c := by
  have hs := Equiv.Perm.mem_cycleFactorsFinset_support_le c.2 ha
  have hc : σ.cycleOf a=c.1 := (Equiv.Perm.cycle_is_cycleOf ha c.2).symm
  simp only [markedBirthChronologicalPivot,hs,dite_true]
  exact congrArg (markedBirthCyclePivot σ) (Subtype.ext hc)

theorem markedBirthChronologicalPivot_sameCycle {a : A} (ha : a∈σ.support) :
    σ.SameCycle a (markedBirthChronologicalPivot σ a) := by
  simp only [markedBirthChronologicalPivot,ha,dite_true]
  exact (Equiv.Perm.mem_support_cycleOf_iff.mp (markedBirthCyclePivot_mem σ
    ⟨σ.cycleOf a,Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr ha⟩)).1

theorem markedBirthChronologicalPivot_mem {a : A} (ha : a∈σ.support) :
    markedBirthChronologicalPivot σ a∈markedBirthCyclePivots σ := by
  simp only [markedBirthChronologicalPivot,ha,dite_true]
  exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

theorem markedBirthChronologicalPivot_fixed {a : A} (ha : a∈markedBirthCyclePivots σ) :
    markedBirthChronologicalPivot σ a=a := by
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp ha
  exact markedBirthChronologicalPivot_of_cycle σ c _ (markedBirthCyclePivot_mem σ c)

theorem markedBirthChronologicalPivot_apply (a : A) :
    markedBirthChronologicalPivot σ (σ a)=markedBirthChronologicalPivot σ a := by
  by_cases ha : a∈σ.support
  · have hs := Equiv.Perm.apply_mem_support.mpr ha
    simp only [markedBirthChronologicalPivot,ha,hs,dite_true]
    exact congrArg (markedBirthCyclePivot σ) (Subtype.ext (Equiv.Perm.cycleOf_self_apply σ a))
  · exact congrArg (markedBirthChronologicalPivot σ) (Equiv.Perm.notMem_support.mp ha)

theorem markedBirthChronologicalPivot_lt {a : A} (ha : a∈markedBirthCycleNonpivots σ) :
    markedBirthChronologicalPivot σ a<a := by
  have hs := (Finset.mem_sdiff.mp ha).1
  have hn := (Finset.mem_sdiff.mp ha).2
  have hle : markedBirthChronologicalPivot σ a≤a := by
    simp only [markedBirthChronologicalPivot,hs,dite_true]
    apply markedBirthCyclePivot_le
    exact Equiv.Perm.mem_support_cycleOf_iff.mpr ⟨Equiv.Perm.SameCycle.rfl,hs⟩
  apply lt_of_le_of_ne hle
  intro he
  exact hn (he ▸ markedBirthChronologicalPivot_mem σ hs)

omit [DecidableEq A] [LinearOrder A] in
theorem markedBirthPermutationEvent_sameCycle (p : A → Option P)
    (hσ : MarkedBirthPermutationEvent p σ) {a b : A} (hab : σ.SameCycle a b) : p a=p b := by
  have hp (k : ℕ) : p ((σ^k) a)=p a := by
    induction k with
    | zero => rfl
    | succ k ih =>
      calc
        _ = p (σ ((σ^k) a)) := by rw [pow_succ',Equiv.Perm.mul_apply]
        _ = p ((σ^k) a) := markedBirthPermutationEvent_value p σ hσ _
        _ = _ := ih
  obtain ⟨k,hk⟩ := hab.exists_nat_pow_eq
  exact (hp k).symm.trans (congrArg p hk)

theorem markedBirthChronologicalPivot_event (p : A → Option P)
    (hσ : MarkedBirthPermutationEvent p σ) {a : A} (ha : a∈markedBirthCycleNonpivots σ) :
    markedBirthChronologicalPivot σ a<a ∧
      markedBirthChronologicalPivot σ a∈σ.support ∧ a∈σ.support ∧
      p a=p (markedBirthChronologicalPivot σ a) ∧ p a≠none := by
  have hs := markedBirthCycleNonpivots_support σ ha
  exact ⟨markedBirthChronologicalPivot_lt σ ha,
    markedBirthCyclePivots_subset σ (markedBirthChronologicalPivot_mem σ hs),hs,
    markedBirthPermutationEvent_sameCycle σ p hσ (markedBirthChronologicalPivot_sameCycle σ hs),
    markedBirthPermutationEvent_performed p σ hσ a hs⟩

theorem markedBirthPermutationEvent_iff_pivots (p : A → Option P) :
    MarkedBirthPermutationEvent p σ ↔
      (∀ a∈σ.support,p a≠none) ∧
      (∀ a∈markedBirthCycleNonpivots σ,p a=p (markedBirthChronologicalPivot σ a)) := by
  constructor
  · intro h
    exact ⟨fun a ha => markedBirthPermutationEvent_performed p σ h a ha,
      fun a ha => (markedBirthChronologicalPivot_event σ p h ha).2.2.2.1⟩
  · rintro ⟨hperformed,heq⟩ a
    by_cases ha : a∈σ.support
    · right
      have hs := Equiv.Perm.apply_mem_support.mpr ha
      have hp (b : A) (hb : b∈σ.support) : p b=p (markedBirthChronologicalPivot σ b) := by
        by_cases hbp : b∈markedBirthCyclePivots σ
        · exact (congrArg p (markedBirthChronologicalPivot_fixed σ hbp)).symm
        · exact heq b (Finset.mem_sdiff.mpr ⟨hb,hbp⟩)
      exact ⟨hperformed _ hs,(hp (σ a) hs).trans
        ((congrArg p (markedBirthChronologicalPivot_apply σ a)).trans (hp a ha).symm)⟩
    · exact Or.inl (Equiv.Perm.notMem_support.mp ha)

end
end ArtinMatthews
