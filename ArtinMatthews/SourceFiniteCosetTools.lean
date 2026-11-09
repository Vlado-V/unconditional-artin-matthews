module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Small finite-coset helpers for the actual lattice quotient. -/
namespace ArtinMatthews.SourcePhysical

open scoped Classical
noncomputable section

def sourceAdditiveCosetRepresentative {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    (p : G →+ Q) (hp : Function.Surjective p) (q : Q) : G :=
  (hp q).choose

theorem sourceAdditiveCosetRepresentative_spec {G Q : Type*} [AddCommGroup G] [AddCommGroup Q]
    (p : G →+ Q) (hp : Function.Surjective p) (q : Q) :
    p (sourceAdditiveCosetRepresentative p hp q) = q :=
  (hp q).choose_spec

def sourceAdditiveCosetEquiv {G Q W : Type*} [AddCommGroup G] [AddCommGroup Q] [AddCommGroup W]
    (p : G →+ Q) (hp : Function.Surjective p) (j : W →+ G) (hj : Function.Injective j)
    (hker : ∀ x, p x = 0 ↔ ∃ y, j y = x) : Q × W ≃ G :=
  Equiv.ofBijective (fun a => sourceAdditiveCosetRepresentative p hp a.1 + j a.2) (by
    have hpoint (q : Q) (y : W) :
        p (sourceAdditiveCosetRepresentative p hp q + j y) = q := by
      rw [map_add, sourceAdditiveCosetRepresentative_spec,
        (hker (j y)).mpr ⟨y, rfl⟩, add_zero]
    constructor
    · rintro ⟨a, u⟩ ⟨b, v⟩ hab
      change sourceAdditiveCosetRepresentative p hp a + j u =
        sourceAdditiveCosetRepresentative p hp b + j v at hab
      have he : a = b := (hpoint a u).symm.trans ((congrArg p hab).trans (hpoint b v))
      subst b
      exact Prod.ext rfl (hj (add_left_cancel hab))
    · intro x
      obtain ⟨y, hy⟩ := (hker (x - sourceAdditiveCosetRepresentative p hp (p x))).mp
        (by rw [map_sub, sourceAdditiveCosetRepresentative_spec, sub_self])
      refine ⟨(p x, y), ?_⟩
      change sourceAdditiveCosetRepresentative p hp (p x) + j y = x
      rw [hy, add_sub_cancel])

@[simp] theorem sourceAdditiveCosetEquiv_apply {G Q W : Type*}
    [AddCommGroup G] [AddCommGroup Q] [AddCommGroup W]
    (p : G →+ Q) (hp : Function.Surjective p) (j : W →+ G) (hj : Function.Injective j)
    (hker : ∀ x, p x = 0 ↔ ∃ y, j y = x) (q : Q) (y : W) :
    sourceAdditiveCosetEquiv p hp j hj hker (q, y) =
      sourceAdditiveCosetRepresentative p hp q + j y := rfl

theorem sourceFiniteCoset_summable_norm {Q W X : Type*} [Finite Q]
    (e : Q × W ≃ X) (f : X → ℂ) (hf : ∀ q, Summable fun y => ‖f (e (q, y))‖) :
    Summable fun x => ‖f x‖ := by
  apply e.summable_iff.mp
  exact (summable_prod_of_nonneg (fun a => norm_nonneg (f (e a)))).mpr
    ⟨hf, summable_of_hasFiniteSupport (Set.toFinite _)⟩

theorem sourceFiniteCoset_tsum {Q W X : Type*} [Finite Q]
    (e : Q × W ≃ X) (f : X → ℂ) (hf : ∀ q, Summable fun y => ‖f (e (q, y))‖) :
    (∑' x, f x) = ∑' q, ∑' y, f (e (q, y)) := by
  rw [← e.tsum_eq f]
  exact (e.summable_iff.mpr (sourceFiniteCoset_summable_norm e f hf).of_norm).tsum_prod

end
end ArtinMatthews.SourcePhysical
