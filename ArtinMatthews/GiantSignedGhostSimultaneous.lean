module

public import ArtinMatthews.GiantSignedGhostMemoryCoordinates
public import ArtinMatthews.FiniteProductAbsolute


set_option backward.privateInPublic true
@[expose] public section

/-! The literal simultaneous ordered-deletion and ordered-birth row. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

abbrev GiantSignedGhostProductMoves {B : Type*} {P : B → Finset ℕ}
    (x : GiantSignedMemoryGroups P) :=
  (g : B) → GiantSignedGhostMoves (x g)

def giantSignedGhostProductMoveTarget {B : Type*} {P : B → Finset ℕ}
    (x : GiantSignedMemoryGroups P) (r : GiantSignedGhostProductMoves x) :
    GiantSignedMemoryGroups P := fun g => giantSignedGhostMoveTarget (x g) (r g)

def giantSignedGhostProductMoveCoefficient {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (A C D : B → ℂ)
    (x : GiantSignedMemoryGroups P) (r : GiantSignedGhostProductMoves x) : ℂ :=
  ∏ g, giantSignedGhostMoveCoefficient (ν g) (A g) (C g) (D g) (x g) (r g)

def giantSignedGhostProductSimultaneousApply {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (A C D : B → ℂ) (f : GiantSignedMemoryGroups P → ℂ)
    (x : GiantSignedMemoryGroups P) : ℂ :=
  ∑' r : GiantSignedGhostProductMoves x,
    giantSignedGhostProductMoveCoefficient ν A C D x r * f (giantSignedGhostProductMoveTarget x r)

abbrev GiantSignedGhostMemoryMoves {B : Type*} {P : B → Finset ℕ}
    (m : GiantSignedMemory P) :=
  GiantSignedGhostProductMoves (giantSignedMemoryGroupEquiv P m)

def giantSignedGhostMemoryMoveTarget {B : Type*} {P : B → Finset ℕ}
    (m : GiantSignedMemory P) (r : GiantSignedGhostMemoryMoves m) : GiantSignedMemory P :=
  (giantSignedMemoryGroupEquiv P).symm
    (giantSignedGhostProductMoveTarget (giantSignedMemoryGroupEquiv P m) r)

theorem giantSignedGhostMemoryMoveTarget_degree {B : Type*} {P : B → Finset ℕ}
    (m : GiantSignedMemory P) (r : GiantSignedGhostMemoryMoves m) (g : B) :
    (giantSignedGhostMemoryMoveTarget m r).1 g =
      (giantSignedGhostMoveTarget (giantSignedMemoryGroupEquiv P m g) (r g)).1 := rfl

def giantSignedGhostMemoryMoveCoefficient {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (A C D : B → ℂ)
    (m : GiantSignedMemory P) (r : GiantSignedGhostMemoryMoves m) : ℂ :=
  giantSignedGhostProductMoveCoefficient ν A C D (giantSignedMemoryGroupEquiv P m) r

def giantSignedGhostSimultaneousApply {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (A C D : B → ℂ) (f : GiantSignedMemory P → ℂ)
    (m : GiantSignedMemory P) : ℂ :=
  ∑' r : GiantSignedGhostMemoryMoves m,
    giantSignedGhostMemoryMoveCoefficient ν A C D m r * f (giantSignedGhostMemoryMoveTarget m r)

theorem giantSignedGhostSimultaneous_summable_norm
    {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (Cf u : ℝ) (_hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) (m : GiantSignedMemory P) :
    Summable (fun r : GiantSignedGhostMemoryMoves m =>
      ‖giantSignedGhostMemoryMoveCoefficient ν A C D m r * f (giantSignedGhostMemoryMoveTarget m r)‖) := by
  classical
  let x := giantSignedMemoryGroupEquiv P m
  let w := fun g (r : GiantSignedGhostMoves (x g)) =>
    ‖giantSignedGhostMoveCoefficient (ν g) (A g) (C g) (D g) (x g) r‖ *
      u ^ (giantSignedGhostMoveTarget (x g) r).1
  have hw0 : ∀ g r, 0 ≤ w g r := fun g r =>
    mul_nonneg (norm_nonneg _) (pow_nonneg hu.le _)
  have hw : ∀ g, Summable (w g) := fun g =>
    giantSignedGhostMoves_norm_weight_summable (ν g) (hν g) (A g) (C g) (D g)
      (fun t => u ^ t.1) (fun _ => pow_nonneg hu.le _) 1 u zero_le_one hu.le
      (fun _ => by simp only [one_mul]; exact le_rfl) (x g)
  apply ((finiteProduct_summable_nonneg _ w hw0 hw).mul_left Cf).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro r
  rw [norm_mul, giantSignedGhostMemoryMoveCoefficient, giantSignedGhostProductMoveCoefficient, norm_prod]
  calc
    _ ≤ (∏ g, ‖giantSignedGhostMoveCoefficient (ν g) (A g) (C g) (D g) (x g) (r g)‖) *
        (Cf * u ^ (∑ g, (giantSignedGhostMemoryMoveTarget m r).1 g)) :=
      mul_le_mul_of_nonneg_left (hf _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by
      simp only [giantSignedGhostMemoryMoveTarget_degree]
      dsimp only [w, x]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring

theorem giantSignedGhostProductSimultaneous_summable_norm
    {B : Type*} [Fintype B] {P : B → Finset ℕ}
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemoryGroups P → ℂ) (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ x, ‖f x‖ ≤ Cf * u ^ (∑ g, (x g).1)) (x : GiantSignedMemoryGroups P) :
    Summable (fun r : GiantSignedGhostProductMoves x =>
      ‖giantSignedGhostProductMoveCoefficient ν A C D x r * f (giantSignedGhostProductMoveTarget x r)‖) := by
  obtain ⟨m, rfl⟩ := (giantSignedMemoryGroupEquiv P).surjective x
  have h := giantSignedGhostSimultaneous_summable_norm ν hν A C D
    (fun m => f (giantSignedMemoryGroupEquiv P m)) Cf u hCf hu
    (fun m => hf (giantSignedMemoryGroupEquiv P m)) m
  simpa only [GiantSignedGhostMemoryMoves, giantSignedGhostMemoryMoveCoefficient, giantSignedGhostMemoryMoveTarget,
    Equiv.apply_symm_apply] using h

end
end ArtinMatthews
