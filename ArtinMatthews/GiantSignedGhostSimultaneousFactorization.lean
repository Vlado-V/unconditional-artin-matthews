module

public import ArtinMatthews.FiniteDependentTsumSplit
public import ArtinMatthews.GiantSignedGhostSimultaneous
public import ArtinMatthews.GiantSignedGhostCoordinateApply


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Fubini for the literal simultaneous ordered ghost moves. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}

def giantSignedGhostMovesSplit (x : GiantSignedMemoryGroups P) (g : B) :
    GiantSignedGhostProductMoves x ≃
      GiantSignedGhostMoves (x g) ×
        GiantSignedGhostProductMoves (fun h : {h : B // h ≠ g} => x h) :=
  Equiv.piSplitAt g (fun h => GiantSignedGhostMoves (x h))

omit [Fintype B] in
theorem giantSignedGhostProductMoveTarget_split
    (x : GiantSignedMemoryGroups P) (g : B)
    (r : GiantSignedGhostMoves (x g))
    (s : GiantSignedGhostProductMoves (fun h : {h : B // h ≠ g} => x h)) :
    giantSignedGhostProductMoveTarget x ((giantSignedGhostMovesSplit x g).symm (r, s)) =
      (giantSignedMemorySplit P g).symm
        (giantSignedGhostMoveTarget (x g) r,
          giantSignedGhostProductMoveTarget (fun h : {h : B // h ≠ g} => x h) s) := by
  funext h
  by_cases hh : h = g
  · subst h
    simp [giantSignedGhostProductMoveTarget, giantSignedGhostMovesSplit,
      giantSignedMemorySplit, Equiv.piSplitAt]
  · simp [giantSignedGhostProductMoveTarget, giantSignedGhostMovesSplit,
      giantSignedMemorySplit, Equiv.piSplitAt, hh]

theorem giantSignedGhostProductMoveCoefficient_split
    (ν : ∀ g, P g → ℝ) (A C D : B → ℂ)
    (x : GiantSignedMemoryGroups P) (g : B)
    (r : GiantSignedGhostMoves (x g))
    (s : GiantSignedGhostProductMoves (fun h : {h : B // h ≠ g} => x h)) :
    giantSignedGhostProductMoveCoefficient ν A C D x
        ((giantSignedGhostMovesSplit x g).symm (r, s)) =
      giantSignedGhostMoveCoefficient (ν g) (A g) (C g) (D g) (x g) r *
        giantSignedGhostProductMoveCoefficient
          (fun h : {h : B // h ≠ g} => ν h) (fun h => A h) (fun h => C h) (fun h => D h)
          (fun h => x h) s := by
  unfold giantSignedGhostProductMoveCoefficient
  rw [giantSignedProduct_split g]
  congr 1
  · simp [giantSignedGhostMovesSplit, Equiv.piSplitAt]
  · apply Finset.prod_congr rfl
    intro h _
    simp [giantSignedGhostMovesSplit, Equiv.piSplitAt, h.property]

omit [DecidableEq B] in
theorem giantSignedGhostProductSimultaneous_summable
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemoryGroups P → ℂ) (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ x, ‖f x‖ ≤ Cf * u ^ (∑ g, (x g).1)) (x : GiantSignedMemoryGroups P) :
    Summable (fun r : GiantSignedGhostProductMoves x =>
      giantSignedGhostProductMoveCoefficient ν A C D x r *
        f (giantSignedGhostProductMoveTarget x r)) :=
  (giantSignedGhostProductSimultaneous_summable_norm ν hν A C D f Cf u hCf hu hf x).of_norm

theorem giantSignedGhostProductSimultaneous_split
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemoryGroups P → ℂ) (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ x, ‖f x‖ ≤ Cf * u ^ (∑ g, (x g).1))
    (x : GiantSignedMemoryGroups P) (g : B) :
    giantSignedGhostProductSimultaneousApply ν A C D f x =
      ∑' r : GiantSignedGhostMoves (x g),
        giantSignedGhostMoveCoefficient (ν g) (A g) (C g) (D g) (x g) r *
          giantSignedGhostProductSimultaneousApply
            (fun h : {h : B // h ≠ g} => ν h) (fun h => A h) (fun h => C h) (fun h => D h)
            (fun y => f ((giantSignedMemorySplit P g).symm
              (giantSignedGhostMoveTarget (x g) r, y))) (fun h => x h) := by
  let F := fun r : GiantSignedGhostProductMoves x =>
    giantSignedGhostProductMoveCoefficient ν A C D x r *
      f (giantSignedGhostProductMoveTarget x r)
  have hs : Summable F :=
    giantSignedGhostProductSimultaneous_summable ν hν A C D f Cf u hCf hu hf x
  calc
    _ = ∑' r : GiantSignedGhostMoves (x g),
        ∑' s : GiantSignedGhostProductMoves (fun h : {h : B // h ≠ g} => x h),
          F ((giantSignedGhostMovesSplit x g).symm (r, s)) :=
      finiteDependentTsum_split (fun h => GiantSignedGhostMoves (x h)) g F hs
    _ = _ := by
      apply tsum_congr
      intro r
      simp only [F, giantSignedGhostProductMoveCoefficient_split,
        giantSignedGhostProductMoveTarget_split, giantSignedGhostProductSimultaneousApply]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro s
      ring

theorem giantSignedGhostProductSimultaneous_split_reverse
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (f : GiantSignedMemoryGroups P → ℂ) (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ x, ‖f x‖ ≤ Cf * u ^ (∑ g, (x g).1))
    (x : GiantSignedMemoryGroups P) (g : B) :
    giantSignedGhostProductSimultaneousApply ν A C D f x =
      ∑' s : GiantSignedGhostProductMoves (fun h : {h : B // h ≠ g} => x h),
        giantSignedGhostProductMoveCoefficient
          (fun h : {h : B // h ≠ g} => ν h) (fun h => A h) (fun h => C h) (fun h => D h)
          (fun h => x h) s *
        giantSignedGhostGroupApply (ν g) (A g) (C g) (D g)
          (fun t => f ((giantSignedMemorySplit P g).symm
            (t, giantSignedGhostProductMoveTarget (fun h : {h : B // h ≠ g} => x h) s)))
          (x g) := by
  let F := fun r : GiantSignedGhostProductMoves x =>
    giantSignedGhostProductMoveCoefficient ν A C D x r *
      f (giantSignedGhostProductMoveTarget x r)
  have hs : Summable F :=
    giantSignedGhostProductSimultaneous_summable ν hν A C D f Cf u hCf hu hf x
  calc
    _ = ∑' s : GiantSignedGhostProductMoves (fun h : {h : B // h ≠ g} => x h),
        ∑' r : GiantSignedGhostMoves (x g),
          F ((giantSignedGhostMovesSplit x g).symm (r, s)) :=
      finiteDependentTsum_split_reverse (fun h => GiantSignedGhostMoves (x h)) g F hs
    _ = _ := by
      apply tsum_congr
      intro s
      let y := giantSignedGhostProductMoveTarget (fun h : {h : B // h ≠ g} => x h) s
      have hslice : ∀ t, ‖f ((giantSignedMemorySplit P g).symm (t, y))‖ ≤
          (Cf * u ^ (∑ h : {h : B // h ≠ g}, (y h).1)) * u ^ t.1 :=
        giantSignedGhostProduct_slice_bound f Cf u hf g y
      have hgroup := giantSignedGhostMoves_tsum (ν g) (hν g) (A g) (C g) (D g)
        (fun t => f ((giantSignedMemorySplit P g).symm (t, y)))
        (Cf * u ^ (∑ h : {h : B // h ≠ g}, (y h).1)) u
        (mul_nonneg hCf (pow_nonneg hu.le _)) hu.le hslice (x g)
      simp only [F, giantSignedGhostProductMoveCoefficient_split,
        giantSignedGhostProductMoveTarget_split]
      rw [← hgroup, ← tsum_mul_left]
      apply tsum_congr
      intro r
      dsimp only [y]
      ring

end
end ArtinMatthews
