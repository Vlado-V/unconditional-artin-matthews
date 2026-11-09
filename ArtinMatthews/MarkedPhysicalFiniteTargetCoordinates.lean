module

public import ArtinMatthews.MarkedPhysicalRootTargetReindex


set_option backward.privateInPublic true
@[expose] public section

/-! The actual unimodular target-coordinate map restricted to the finite
original target set. It is a genuine equivalence with its exact image. -/
namespace ArtinMatthews
noncomputable section
open scoped Classical

def markedPhysicalFiniteTargetEquiv {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1<A) (hC : 1<C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) : Z ≃ ↥(markedPhysicalCanonicalTargets hA hC r Z) where
  toFun z := ⟨markedPhysicalCanonicalTargetEquiv hA hC r z.1,
    Finset.mem_image.mpr ⟨z.1,z.2,rfl⟩⟩
  invFun z := ⟨(markedPhysicalCanonicalTargetEquiv hA hC r).symm z.1,
    (markedPhysicalCanonicalTargets_mem hA hC r Z z.1).mp z.2⟩
  left_inv z := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _
  right_inv z := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _

theorem markedPhysicalFiniteTargetEquiv_apply {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1<A) (hC : 1<C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) (z : Z) :
    ((markedPhysicalFiniteTargetEquiv hA hC r Z) z).1=
      markedPhysicalRootCoordinates (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r) z.1 := rfl

theorem markedPhysicalFiniteTargetEquiv_symm_apply {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1<A) (hC : 1<C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) (z : markedPhysicalCanonicalTargets hA hC r Z) :
    ((markedPhysicalFiniteTargetEquiv hA hC r Z).symm z).1=
      markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r) z.1 := rfl

theorem markedPhysicalCanonicalTargets_card {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1<A) (hC : 1<C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) : (markedPhysicalCanonicalTargets hA hC r Z).card=Z.card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (markedPhysicalFiniteTargetEquiv hA hC r Z)).symm

end
end ArtinMatthews
