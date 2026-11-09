module

public import ArtinMatthews.MarkedBonferroniTail


set_option backward.privateInPublic true
@[expose] public section

/-! The literal truncation depth pays every fixed power of the logarithm. -/

namespace ArtinMatthews

open Filter
open scoped Topology

/-- The squared error envelope for the truncated marked-divisor model is
smaller than any fixed log power at depth (lfloor L^{1/100}
floor). -/
theorem sourceComparison_divisorErrorBudget_log_saving (D E A : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (C V : ℝ), 0 ≤ C → C ≤ L^D → V ≤ E*Real.log L →
      C^2/(2:ℝ)^(⌊L^(1/(100:ℝ))⌋₊+1) * Real.exp ((8*Real.exp 2-1)*V) ≤ L^(-A) := by
  let K := 8*Real.exp 2-1
  have hK : 0 ≤ K := by
    dsimp [K]
    linarith [Real.one_le_exp (by norm_num : (0:ℝ) ≤ 2)]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlim := rpow_mul_exp_neg_rpow_tendsto (2*D+K*E+A)
    (show (0:ℝ) < 1/100 by norm_num) hlog2
  filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one),
    eventually_gt_atTop (0:ℝ)] with L hlim hL
  intro C V hC hCD hV
  have hn : L^(1/(100:ℝ)) ≤ ((⌊L^(1/(100:ℝ))⌋₊+1:ℕ):ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (L^(1/(100:ℝ)))).le
  have hdec : ((2:ℝ)^(⌊L^(1/(100:ℝ))⌋₊+1))⁻¹ ≤
      Real.exp (-Real.log 2*L^(1/(100:ℝ))) := by
    conv_lhs => rw [← Real.exp_log (by norm_num : (0:ℝ) < 2), ← Real.exp_nat_mul, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hn hlog2.le]
  have hE : Real.exp (K*V) ≤ L^(K*E) := by
    rw [Real.rpow_def_of_pos hL]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ K*(E*Real.log L) := mul_le_mul_of_nonneg_left hV hK
      _ = _ := by ring
  have hh : L^(2*D+K*E)*Real.exp (-Real.log 2*L^(1/(100:ℝ))) ≤ L^(-A) := by
    rw [Real.rpow_neg hL.le, ← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hL A)).mpr
    have he : L^(2*D+K*E)*Real.exp (-Real.log 2*L^(1/(100:ℝ)))*L^A =
        L^(2*D+K*E+A)*Real.exp (-Real.log 2*L^(1/(100:ℝ))) := by
      rw [Real.rpow_add hL (2*D+K*E) A]
      ring
    exact he.trans_le hlim.le
  change C^2/(2:ℝ)^(⌊L^(1/(100:ℝ))⌋₊+1)*Real.exp (K*V) ≤ _
  calc
    _ ≤ (L^D)^2*Real.exp (-Real.log 2*L^(1/(100:ℝ)))*L^(K*E) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul (pow_le_pow_left₀ hC hCD 2) hdec
        (by positivity) (by positivity)) hE (by positivity) (by positivity)
    _ = L^(2*D+K*E)*Real.exp (-Real.log 2*L^(1/(100:ℝ))) := by
      rw [Real.rpow_add hL (2*D) (K*E), show 2*D=D*2 by ring,
        Real.rpow_mul hL.le D 2, Real.rpow_two]
      ring
    _ ≤ _ := hh

end ArtinMatthews
