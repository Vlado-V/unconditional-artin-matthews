module

public import ArtinMatthews.MarkedPhysicalRootTargetReindex


set_option backward.privateInPublic true
@[expose] public section

/-! Changing the residue modulus does not change the canonical integer
completion or any relative coordinate. The proof uses the actual
determinant-one equation and the half-open choice of its first entry. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalCanonicalCompletion_eq_of_position_eq
    {S T : ℕ} [NeZero S] [NeZero T] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D)
    (r' : MarkedPhysicalCanonicalRoot T A B C D)
    (he : markedPhysicalCanonicalRootPosition r=markedPhysicalCanonicalRootPosition r') :
    markedPhysicalCanonicalCompletion r=markedPhysicalCanonicalCompletion r' := by
  rcases r with ⟨g,⟨⟨u,c,v⟩,hp⟩⟩
  rcases r' with ⟨g',⟨⟨u',c',v'⟩,hp'⟩⟩
  have hu : u=u' := congrArg Prod.fst he
  have hv : v=v' := congrArg Prod.snd he
  subst u'
  subst v'
  obtain ⟨d,_,_,hc,hcu,_,_,hd,_⟩ :=
    fixedURootReciprocal_box_canonical hA hC (by norm_num) (by norm_num) hp
  obtain ⟨d',_,_,hc',hcu',_,_,hd',_⟩ :=
    fixedURootReciprocal_box_canonical hA hC (by norm_num) (by norm_num) hp'
  have hcc := fixedURoot_canonical_entry_unique hc.le hcu hc'.le hcu' hd hd'
  subst c'
  rfl

def markedPhysicalCanonicalRootChangeModulus
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C) :
    MarkedPhysicalCanonicalRoot S A B C D ≃ MarkedPhysicalCanonicalRoot T A B C D :=
  (markedPhysicalCanonicalRootEquiv (S := S) (B := B) (D := D) hA hC).trans
    (markedPhysicalCanonicalRootEquiv (S := T) (B := B) (D := D) hA hC).symm

theorem markedPhysicalCanonicalRootChangeModulus_position
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D) :
    markedPhysicalCanonicalRootPosition (markedPhysicalCanonicalRootChangeModulus S T hA hC r)=
      markedPhysicalCanonicalRootPosition r := by
  exact congrArg Subtype.val ((markedPhysicalCanonicalRootEquiv (S := T) (B := B) (D := D) hA hC).apply_symm_apply
    ((markedPhysicalCanonicalRootEquiv (S := S) (B := B) (D := D) hA hC) r))

theorem markedPhysicalCanonicalRootChangeModulus_completion
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D) :
    markedPhysicalCanonicalCompletion (markedPhysicalCanonicalRootChangeModulus S T hA hC r)=
      markedPhysicalCanonicalCompletion r :=
  markedPhysicalCanonicalCompletion_eq_of_position_eq hA hC _ _
    (markedPhysicalCanonicalRootChangeModulus_position S T hA hC r)

theorem markedPhysicalCanonicalRootChangeModulus_lift
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot S A B C D) (z : ℤ × ℤ) :
    markedPhysicalRootLift
      (markedPhysicalCanonicalRootPosition (markedPhysicalCanonicalRootChangeModulus S T hA hC r))
      (markedPhysicalCanonicalCompletion (markedPhysicalCanonicalRootChangeModulus S T hA hC r)) z=
      markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r) z := by
  rw [markedPhysicalCanonicalRootChangeModulus_position,markedPhysicalCanonicalRootChangeModulus_completion]

theorem markedPhysicalCanonicalRoot_sum_changeModulus
    (S T : ℕ) [NeZero S] [NeZero T] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (F : (ℤ × ℤ) → (ℤ × ℤ) → ℂ) :
    (∑ r : MarkedPhysicalCanonicalRoot S A B C D,
      F (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r))=
    ∑ r : MarkedPhysicalCanonicalRoot T A B C D,
      F (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r) := by
  calc
    _ = ∑ r : MarkedPhysicalCanonicalRoot S A B C D,
        F (markedPhysicalCanonicalRootPosition (markedPhysicalCanonicalRootChangeModulus S T hA hC r))
          (markedPhysicalCanonicalCompletion (markedPhysicalCanonicalRootChangeModulus S T hA hC r)) := by
      simp only [markedPhysicalCanonicalRootChangeModulus_position,markedPhysicalCanonicalRootChangeModulus_completion]
    _ = _ := Equiv.sum_comp (markedPhysicalCanonicalRootChangeModulus S T hA hC)
      (fun r : MarkedPhysicalCanonicalRoot T A B C D =>
        F (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r))

end
end ArtinMatthews
