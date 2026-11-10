module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

/-- The second dyadic term splits into its product scale and upper endpoint scale. -/
theorem shiftedBilinear_second_scale_identity {M T : ℝ} (hM : 0 < M) (hT : 0 < T) :
    M ^ (5/4:ℝ) * T ^ (7/8:ℝ) = (M*T) ^ (7/8:ℝ) * M ^ (3/8:ℝ) := by
  rw [Real.mul_rpow hM.le hT.le]
  calc
    _ = (M ^ (7/8:ℝ) * M ^ (3/8:ℝ)) * T ^ (7/8:ℝ) := by
      rw [← Real.rpow_add hM]
      norm_num
    _ = _ := by ring

theorem shiftedBilinear_first_scale_le {M T x lo : ℝ}
    (hM : 0 < M) (hT : 0 < T) (hlo : 1 ≤ lo)
    (hloM : lo ≤ 2*M) (hMT : M*T ≤ 2*x) :
    Real.sqrt M*T ≤ 4*x*lo ^ (-1/2:ℝ) := by
  have hlo0 : 0 < lo := zero_lt_one.trans_le hlo
  have hslo : 0 < Real.sqrt lo := Real.sqrt_pos.2 hlo0
  have hroot : Real.sqrt lo ≤ 2*Real.sqrt M := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [Real.sq_sqrt hM.le]
  rw [show (-1/2:ℝ) = -(1/2:ℝ) by ring,
    Real.rpow_neg hlo0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  apply (le_div_iff₀ hslo).mpr
  calc
    _ ≤ (Real.sqrt M*T)*(2*Real.sqrt M) :=
      mul_le_mul_of_nonneg_left hroot (mul_nonneg (Real.sqrt_nonneg _) hT.le)
    _ = 2*(Real.sqrt M)^2*T := by ring
    _ = 2*(M*T) := by rw [Real.sq_sqrt hM.le]; ring
    _ ≤ 4*x := by linarith

theorem shiftedBilinear_second_scale_le {M T x hi : ℝ}
    (hM : 0 < M) (hT : 0 < T) (hx : 1 ≤ x)
    (hMhi : M ≤ hi) (hMT : M*T ≤ 2*x) :
    M ^ (5/4:ℝ) * T ^ (7/8:ℝ) ≤ 2*x ^ (7/8:ℝ)*hi ^ (3/8:ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hhi : 0 < hi := hM.trans_le hMhi
  have hprod : (M*T) ^ (7/8:ℝ) ≤ (2*x) ^ (7/8:ℝ) :=
    Real.rpow_le_rpow (mul_pos hM hT).le hMT (by norm_num)
  have hupper : M ^ (3/8:ℝ) ≤ hi ^ (3/8:ℝ) :=
    Real.rpow_le_rpow hM.le hMhi (by norm_num)
  have htwo : (2:ℝ) ^ (7/8:ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
        (show (7/8:ℝ) ≤ 1 by norm_num)
  rw [shiftedBilinear_second_scale_identity hM hT]
  calc
    _ ≤ (2*x) ^ (7/8:ℝ) * hi ^ (3/8:ℝ) :=
      mul_le_mul hprod hupper (Real.rpow_nonneg hM.le _) (Real.rpow_nonneg (by positivity) _)
    _ = (2:ℝ) ^ (7/8:ℝ) * (x ^ (7/8:ℝ)*hi ^ (3/8:ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hx0.le]
      ring
    _ ≤ 2*(x ^ (7/8:ℝ)*hi ^ (3/8:ℝ)) :=
      mul_le_mul_of_nonneg_right htwo (mul_nonneg (Real.rpow_nonneg hx0.le _)
        (Real.rpow_nonneg hhi.le _))
    _ = _ := by ring

/-- Converts the dyadic product scale without imposing a lower bound on `M*T`. -/
theorem shiftedBilinear_dyadic_scale {M T x lo hi δ : ℝ}
    (hM : 0 < M) (hT : 0 < T) (hx : 1 ≤ x) (hlo : 1 ≤ lo)
    (hloM : lo ≤ 2*M) (hMhi : M ≤ hi) (hMT : M*T ≤ 2*x) (hδ : 0 ≤ δ) :
    (M*T) ^ δ * (Real.sqrt M*T + M ^ (5/4:ℝ)*T ^ (7/8:ℝ)) ≤
      (4*(2:ℝ)^δ)*x^δ*(x*lo^(-1/2:ℝ) + x^(7/8:ℝ)*hi^(3/8:ℝ)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlo0 : 0 < lo := zero_lt_one.trans_le hlo
  have hhi : 0 < hi := hM.trans_le hMhi
  have hfirst := shiftedBilinear_first_scale_le hM hT hlo hloM hMT
  have hsecond := shiftedBilinear_second_scale_le hM hT hx hMhi hMT
  have hbase : Real.sqrt M*T + M^(5/4:ℝ)*T^(7/8:ℝ) ≤
      4*(x*lo^(-1/2:ℝ) + x^(7/8:ℝ)*hi^(3/8:ℝ)) := by
    have hnonneg : 0 ≤ x^(7/8:ℝ)*hi^(3/8:ℝ) :=
      mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hhi.le _)
    nlinarith
  have houter : (M*T)^δ ≤ (2:ℝ)^δ*x^δ := by
    calc
      _ ≤ (2*x)^δ := Real.rpow_le_rpow (mul_pos hM hT).le hMT hδ
      _ = _ := Real.mul_rpow (by norm_num) hx0.le
  calc
    _ ≤ ((2:ℝ)^δ*x^δ)*(4*(x*lo^(-1/2:ℝ) + x^(7/8:ℝ)*hi^(3/8:ℝ))) :=
      mul_le_mul houter hbase (by positivity) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews
