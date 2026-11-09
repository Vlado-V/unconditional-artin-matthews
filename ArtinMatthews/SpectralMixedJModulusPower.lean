module

public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic.FieldSimp


set_option backward.privateInPublic true
@[expose] public section

/-! The exact modulus power from the three-eighths contour and the
one-eighth Weil loss. -/
noncomputable section

namespace ArtinMatthews

theorem spectralMixedJ_modulus_power (q K W A D : ℝ)
    (hq : 0 < q) (hK : 0 < K) (hW : 0 < W) :
    (A*q^(5/8 : ℝ))*(K/(q*W)^2)*(D*(K*(2/(q*W)))^(-1/4 : ℝ)) =
      ((A*K*D/W^2)*(2*K/W)^(-1/4 : ℝ))/q^(9/8 : ℝ) := by
  have hX : K*(2/(q*W)) = (2*K/W)/q := by ring
  have hX0 : 0 < 2*K/W := by positivity
  have hdecay : (K*(2/(q*W)))^(-1/4 : ℝ) =
      (2*K/W)^(-1/4 : ℝ)*q^(1/4 : ℝ) := by
    rw [hX,Real.div_rpow hX0.le hq.le]
    simp only [show (-1/4 : ℝ) = -(1/4) by ring,Real.rpow_neg hq.le,div_inv_eq_mul]
  have hpower : q^(5/8 : ℝ)*q^(1/4 : ℝ)/q^2 = 1/q^(9/8 : ℝ) := by
    calc
      _ = q^((5/8 : ℝ)+(1/4)-(2 : ℝ)) := by
        rw [Real.rpow_sub hq,Real.rpow_add hq,Real.rpow_two]
      _ = q^(-(9/8 : ℝ)) := by norm_num
      _ = _ := by rw [Real.rpow_neg hq.le]; simp only [one_div]
  rw [hdecay,mul_pow]
  calc
    _ = ((A*K*D/W^2)*(2*K/W)^(-1/4 : ℝ))*
        (q^(5/8 : ℝ)*q^(1/4 : ℝ)/q^2) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [hpower]; ring

end ArtinMatthews
