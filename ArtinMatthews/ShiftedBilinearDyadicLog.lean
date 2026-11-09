module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

/-- The exact square of the dyadic count majorant is subpower on `x ≥ 1`. -/
theorem shiftedBilinear_dyadic_log_square_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      (1+Real.log (2*x+1)/Real.log 2)^2 ≤ C*x^ε := by
  let δ := ε/2
  let L := Real.log 2
  let A := 1+Real.log 3/L
  let B := 1/δ/L
  have hδ : 0 < δ := half_pos hε
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := add_nonneg zero_le_one (div_nonneg (Real.log_nonneg (by norm_num)) hL.le)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨(A+B)^2,pow_pos (add_pos_of_nonneg_of_pos hA hB) _,?_⟩
  intro x hx
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hxδ : 1 ≤ x^δ := Real.one_le_rpow hx hδ.le
  have hlog : Real.log (2*x+1) ≤ Real.log 3+x^δ/δ := by
    calc
      _ ≤ Real.log (3*x) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 3+Real.log x := Real.log_mul (by norm_num) hx₀.ne'
      _ ≤ _ := add_le_add le_rfl (Real.log_le_rpow_div hx₀.le hδ)
  have hnonneg : 0 ≤ 1+Real.log (2*x+1)/L :=
    add_nonneg zero_le_one (div_nonneg (Real.log_nonneg (by linarith)) hL.le)
  have hfirst : 1+Real.log (2*x+1)/L ≤ (A+B)*x^δ := by
    calc
      _ ≤ 1+(Real.log 3+x^δ/δ)/L := add_le_add le_rfl (div_le_div_of_nonneg_right hlog hL.le)
      _ = A+B*x^δ := by dsimp [A,B]; ring
      _ ≤ A*x^δ+B*x^δ := add_le_add (le_mul_of_one_le_right hA hxδ) le_rfl
      _ = _ := by ring
  have hpow : (x^δ)^2 = x^ε := by
    rw [← Real.rpow_two,← Real.rpow_mul hx₀.le]
    congr 1
    dsimp [δ]
    ring
  change (1+Real.log (2*x+1)/L)^2 ≤ _
  calc
    _ ≤ ((A+B)*x^δ)^2 := pow_le_pow_left₀ hnonneg hfirst 2
    _ = _ := by rw [mul_pow,hpow]

end ArtinMatthews
