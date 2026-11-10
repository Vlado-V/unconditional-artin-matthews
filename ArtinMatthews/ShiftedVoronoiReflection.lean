module

public import ArtinMatthews.ShiftedVoronoiModularity
public import Mathlib.Analysis.MellinTransform
public import ArtinMatthews.ShiftedVoronoiMellin


set_option backward.privateInPublic true
@[expose] public section

/-!
# Mellin reflection derived from actual weight-one modularity

The positive-axis identity is discharged from the slash-invariant form and
matrix membership, rather than added as a functional-equation hypothesis.
The Mellin integrals here are totalized: their convergence, and the subsequent
Bessel inversion for a general test function, are not claimed in this file.
-/

noncomputable section
open Complex UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

/-- Restriction to the vertical line above `x`, extended by zero at nonpositive
heights so that it is a function on the domain used by the Mellin transform. -/
def cuspVerticalRestriction {F : Type*} [FunLike F ℍ ℂ] (f : F) (x : ℝ) : ℝ → ℂ :=
  fun y ↦ if hy : 0 < y then f (cuspVerticalPoint x y hy) else 0

/-- The reflected Mellin identity at a rational cusp follows from actual
weight-one modularity. The scale is `q²` and the scalar is exactly `i/q`. -/
theorem weightOne_vertical_mellin_reflection {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup SL(2, ℤ)} [SlashInvariantFormClass F Γ 1]
    (f : F) (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (hq : γ 1 0 ≠ 0) (s : ℂ) :
    mellin (cuspVerticalRestriction f ((γ 0 0 : ℝ) / γ 1 0)) s =
      (Complex.I / (γ 1 0 : ℂ)) * (((γ 1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 - s) *
        mellin (cuspVerticalRestriction f (-(γ 1 1 : ℝ) / γ 1 0)) (1 - s) := by
  apply mellin_weight_reflection_of_identity
    _ _ _ 1 s ((γ 1 0 : ℝ) ^ 2) (sq_pos_of_ne_zero (by exact_mod_cast hq))
  intro y hy
  have hqC : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hq
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hdual : 0 < ((γ 1 0 : ℝ) ^ 2 * y)⁻¹ :=
    inv_pos.mpr (mul_pos (sq_pos_of_ne_zero (by exact_mod_cast hq)) hy)
  simp only [cuspVerticalRestriction, dite_eq_left hy, dite_eq_left hdual,
    Complex.cpow_neg_one]
  rw [weightOne_cusp_transform f γ hγ y hq hy]
  simp only [one_div]
  field_simp

end ArtinMatthews
