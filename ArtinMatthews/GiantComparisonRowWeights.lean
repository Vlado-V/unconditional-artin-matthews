module

public import ArtinMatthews.GiantComparisonFreeMarking
public import ArtinMatthews.SourceComparisonFreeHit
public import Mathlib.NumberTheory.DirichletCharacter.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! The row envelope keeps the right character in its endpoint
coefficient and bounds the remaining auxiliary character by one. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section

theorem giantComparisonOrderedFreeWeight_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k : ℕ} (C : J → Finset (Fin k)) (ell w : ℕ)
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ giantComparisonOrderedFreeWeight P C ell q w := by
  unfold giantComparisonOrderedFreeWeight giantComparisonQuotientDamping
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (giantTwoSidedPatternFreshMass_nonneg C ell hV)) (pow_nonneg hq _)

theorem giantComparisonPositionKernel_weight_norm_le {m : ℕ} [NeZero m]
    (x : ℝ) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n) (d w : ℕ) :
    ‖giantComparisonPositionKernel x Ψ χ F G d w‖*W w*W (w+d) ≤
      sourceComparisonFreeHitWeight Ψ (fun n => F n*(W n:ℂ))
        (fun n => (χ n*G n)*(W n:ℂ)) (x*(d:ℝ)) d w := by
  let B := sourceComparisonFreeHitWeight Ψ (fun n => F n*(W n:ℂ))
    (fun n => (χ n*G n)*(W n:ℂ)) (x*(d:ℝ)) d w
  have hB : 0 ≤ B := sourceComparisonFreeHitWeight_nonneg _ _ _ _ _ _
  calc
    _ = B*‖χ (d:ℕ)‖ := by
      simp only [B,giantComparisonPositionKernel,sourceComparisonFreeHitWeight,
        norm_mul,norm_div,Complex.norm_natCast,Complex.norm_conj,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (hW w),abs_of_nonneg (hW (w+d))]
      ring
    _ ≤ B := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (χ.norm_le_one (d:ZMod m)) hB

end
end ArtinMatthews
