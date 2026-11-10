module

public import ArtinMatthews.SourceHilbertPencil
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import ArtinMatthews.SourceHilbertFormDefect
public import ArtinMatthews.SourceHilbertRegularInverse
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Eisenstein.MeromorphicResolvent


set_option backward.privateInPublic true
@[expose] public section

/-! The Gram pencil is invertible in the negative and nonreal regions.
The forced vector satisfies the actual variational equation at a unit. -/

namespace ArtinMatthews.HilbertResolvent

open scoped InnerProductSpace NNReal
noncomputable section

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem adjoint_comp_selfAdjoint (j : V →L[ℂ] H) : IsSelfAdjoint (j.adjoint.comp j) := by
  simp [ContinuousLinearMap.isSelfAdjoint_iff']

theorem pencil_isUnit_nonreal (T : V →L[ℂ] V) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (pencil T z) :=
  OAI.CubicEisenstein.selfAdjoint_pencil_isUnit_nonreal T hT (z + 1) (by simpa using hz)

theorem pencil_inverse_analyticAt_of_isUnit (T : V →L[ℂ] V) (z : ℂ)
    (hz : IsUnit (pencil T z)) : AnalyticAt ℂ (fun w => Ring.inverse (pencil T w)) z :=
  ((analyticOnNhd_inverse (𝕜 := ℂ) (A := V →L[ℂ] V)) (pencil T z) hz).comp_of_eq
    (pencil_analyticAt T z) rfl

theorem pencil_adjoint_comp_isUnit_of_neg (j : V →L[ℂ] H) (hj : ‖j‖ ≤ 1)
    (t : ℝ) (ht : t < 0) : IsUnit (pencil (j.adjoint.comp j) (t : ℂ)) := by
  let c : ℝ≥0 := ⟨min 1 (-t), le_min (by norm_num) (by linarith)⟩
  have hc : 0 < c := by
    apply NNReal.coe_pos.mp
    exact lt_min (by norm_num) (neg_pos.mpr ht)
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ hc
  intro x
  have hnorm : ‖j x‖ ≤ ‖x‖ := calc
    ‖j x‖ ≤ ‖j‖ * ‖x‖ := j.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hj (norm_nonneg x)
    _ = ‖x‖ := one_mul _
  have hsq : ‖j x‖ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hq : min 1 (-t) * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - (t + 1) * ‖j x‖ ^ 2 := by
    by_cases hp : 0 ≤ t + 1
    · calc
        _ ≤ (-t) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
        _ = ‖x‖ ^ 2 - (t + 1) * ‖x‖ ^ 2 := by ring
        _ ≤ _ := sub_le_sub_left (mul_le_mul_of_nonneg_left hsq hp) _
    · calc
        _ ≤ 1 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
        _ ≤ _ := by linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) (sq_nonneg ‖j x‖)]
  have he : (inner ℂ (pencil (j.adjoint.comp j) (t : ℂ) x) x).re =
      ‖x‖ ^ 2 - (t + 1) * ‖j x‖ ^ 2 :=
    (inner_re_symm (𝕜 := ℂ) (pencil (j.adjoint.comp j) (t : ℂ) x) x).trans
      (pencil_adjoint_comp_re_inner j t x)
  rw [mul_comm]
  calc
    min 1 (-t) * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - (t + 1) * ‖j x‖ ^ 2 := hq
    _ = (inner ℂ (pencil (j.adjoint.comp j) (t : ℂ) x) x).re := he.symm
    _ ≤ _ := Complex.re_le_norm _

theorem pencil_adjoint_comp_inner_right (j : V →L[ℂ] H) (z : ℂ) (w v : V) :
    inner ℂ w (pencil (j.adjoint.comp j) z v) =
      inner ℂ w v - (z + 1) * inner ℂ (j w) (j v) := by
  change inner ℂ w (v - (z + 1) • j.adjoint (j v)) = _
  rw [inner_sub_right, inner_smul_right, j.adjoint_inner_right]

def forcedVector (j : V →L[ℂ] H) (z : ℂ) (d : H) : V :=
  -(Ring.inverse (pencil (j.adjoint.comp j) z) (j.adjoint d))

theorem forcedVector_solves (j : V →L[ℂ] H) (z : ℂ) (d : H)
    (hz : IsUnit (pencil (j.adjoint.comp j) z)) :
    pencil (j.adjoint.comp j) z (forcedVector j z d) = -(j.adjoint d) := by
  have h := congrArg (fun A : V →L[ℂ] V => A (j.adjoint d))
    (Ring.mul_inverse_cancel (pencil (j.adjoint.comp j) z) hz)
  change pencil (j.adjoint.comp j) z (Ring.inverse (pencil (j.adjoint.comp j) z) (j.adjoint d)) =
    j.adjoint d at h
  rw [forcedVector, map_neg, h]

theorem forcedVector_variational (j : V →L[ℂ] H) (z : ℂ) (d : H)
    (hz : IsUnit (pencil (j.adjoint.comp j) z)) (w : V) :
    inner ℂ w (forcedVector j z d) - (z + 1) * inner ℂ (j w) (j (forcedVector j z d)) =
      -(inner ℂ (j w) d) := by
  have h := congrArg (fun v : V => inner ℂ w v) (forcedVector_solves j z d hz)
  simpa only [pencil_adjoint_comp_inner_right, inner_neg_right, j.adjoint_inner_right] using h

end
end ArtinMatthews.HilbertResolvent
