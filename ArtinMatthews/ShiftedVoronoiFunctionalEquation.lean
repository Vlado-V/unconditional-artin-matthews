module

public import ArtinMatthews.ShiftedVoronoiReflection
public import ArtinMatthews.ShiftedVoronoiConvergence
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

/-!
# A convergent Mellin functional equation at rational cusps

This combines the exact weight-one modular transformation with the independently
proved convergence of the Mellin integral at every complex parameter.
-/

noncomputable section
open Complex UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

/-- A genuine `HasMellin` statement, with convergence discharged by cuspidality
and arithmeticity. The matrix-membership condition supplies modularity. -/
theorem weightOne_cusp_hasMellin
    {Γ : Subgroup SL(2, ℤ)} [(Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic]
    (f : CuspForm Γ 1) (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (hq : γ 1 0 ≠ 0) (s : ℂ) :
    HasMellin (cuspVerticalRestriction f ((γ 0 0 : ℝ) / γ 1 0)) s
      ((Complex.I / (γ 1 0 : ℂ)) * (((γ 1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 - s) *
        mellin (cuspVerticalRestriction f (-(γ 1 1 : ℝ) / γ 1 0)) (1 - s)) := by
  refine ⟨?_, weightOne_vertical_mellin_reflection f γ hγ hq s⟩
  simpa only [Rat.cast_div, Rat.cast_intCast] using
    cuspVerticalRestriction_mellinConvergent (by norm_num) f
      ((γ 0 0 : ℚ) / γ 1 0) s

end ArtinMatthews
