module

public import ArtinMatthews.SourceThetaSchlafliMoments
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import ArtinMatthews.SourceThetaSchlafliDerivatives
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Iterating the actual differentiated Schläfli moments gives every
log derivative without an assumed derivative bound. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory
open scoped ContDiff
noncomputable section

def sourceThetaSchlafliEuler (scale : ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, k, x => sourceThetaSchlafliMoment scale k x
  | n + 1, k, x => ((5 / 6 : ℝ) + k) * sourceThetaSchlafliEuler scale n k x -
      sourceThetaSchlafliEuler scale n (k + 1) x

theorem sourceThetaSchlafliEuler_hasDerivAt {scale : ℝ} (hscale : 0 < scale) (n k : ℕ) (x : ℝ) :
    HasDerivAt (sourceThetaSchlafliEuler scale n k) (sourceThetaSchlafliEuler scale (n + 1) k x) x := by
  induction n generalizing k with
  | zero => exact sourceThetaSchlafliMoment_hasDerivAt hscale k x
  | succ n ih =>
    exact ((ih k).const_mul ((5 / 6 : ℝ) + k)).sub (ih (k + 1))

theorem sourceThetaSchlafliEuler_weighted {scale : ℝ} (hscale : 0 < scale) (n k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖sourceThetaSchlafliEuler scale n k x‖ ≤ C * Real.exp (((5 / 6 : ℝ) - N) * x) := by
  induction n generalizing k with
  | zero => exact sourceThetaSchlafliMoment_weighted hscale k N
  | succ n ih =>
    obtain ⟨C, hC, hb⟩ := ih k
    obtain ⟨D, hD, hd⟩ := ih (k + 1)
    let c := (5 / 6 : ℝ) + k
    have hc : 0 ≤ c := by dsimp only [c]; positivity
    refine ⟨c * C + D, add_nonneg (mul_nonneg hc hC) hD, fun x => ?_⟩
    calc
      _ ≤ ‖c * sourceThetaSchlafliEuler scale n k x‖ +
          ‖sourceThetaSchlafliEuler scale n (k + 1) x‖ := norm_sub_le _ _
      _ = c * ‖sourceThetaSchlafliEuler scale n k x‖ +
          ‖sourceThetaSchlafliEuler scale n (k + 1) x‖ := by
        rw [norm_mul, Real.norm_of_nonneg hc]
      _ ≤ c * (C * Real.exp (((5 / 6 : ℝ) - N) * x)) +
          D * Real.exp (((5 / 6 : ℝ) - N) * x) :=
        add_le_add (mul_le_mul_of_nonneg_left (hb x) hc) (hd x)
      _ = _ := by ring

theorem sourceThetaSchlafliEuler_twoEnded {scale : ℝ} (hscale : 0 < scale) (n k : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖sourceThetaSchlafliEuler scale n k x‖ ≤ C * min (Real.exp ((5 / 6 : ℝ) * x)) (Real.exp (-A * x)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (A + 5 / 6)
  obtain ⟨C₁, hC₁, h₁⟩ := sourceThetaSchlafliEuler_weighted hscale n k 0
  obtain ⟨C₂, hC₂, h₂⟩ := sourceThetaSchlafliEuler_weighted hscale n k N
  let C := max C₁ C₂
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨C, hC, fun x => ?_⟩
  rw [mul_min_of_nonneg _ _ hC]
  apply le_min
  · exact (by simpa using h₁ x : _ ≤ C₁ * Real.exp ((5 / 6 : ℝ) * x)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · rcases le_total x 0 with hx | hx
    · have hExp : Real.exp ((5 / 6 : ℝ) * x) ≤ Real.exp (-A * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (by linarith) hx)
      exact (by simpa using h₁ x : _ ≤ C₁ * Real.exp ((5 / 6 : ℝ) * x)).trans
        ((mul_le_mul_of_nonneg_left hExp hC₁).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
    · have hExp : Real.exp (((5 / 6 : ℝ) - N) * x) ≤ Real.exp (-A * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hx)
      exact (h₂ x).trans ((mul_le_mul_of_nonneg_left hExp hC₂).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le))

end
end ArtinMatthews.SourceReflection
