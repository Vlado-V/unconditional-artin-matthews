module

public import ArtinMatthews.GiantTwoSidedRootRelative


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine source moment length leaves logarithmic room to sum
the relative root error against a fixed-power-per-edge path mass. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

theorem giantCandidateRootError_absorb {C G γ : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hγ : 0<γ) :
    ∀ᶠ x : ℝ in atTop,
      let L := Real.log x
      let n := (giantTwoSidedSourceMomentLength x:ℝ)
      (2*L^(-(C+G+1)*n)+Real.exp (-γ*L/4))*L^(C*n) ≤ L^(-G*n) := by
  have hγ8 : 0<γ/8 := by linarith
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/100)).bound
    (zero_lt_one : (0:ℝ)<1)
  have hdecay := (tendsto_rpow_neg_atTop hγ8).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [marked_sublinear_log_exp_le_rpow_eventually (53/100) (4*(C+G)) (γ/8)
      (by norm_num) hγ8,Real.tendsto_log_atTop.eventually hlog,
    Real.tendsto_log_atTop.eventually_ge_atTop (4:ℝ),eventually_gt_atTop (1:ℝ),hdecay]
    with x hsub hlog hL4 hx hdecay
  let L := Real.log x
  let n := (giantTwoSidedSourceMomentLength x:ℝ)
  have hL : 1 ≤ L := le_trans (by norm_num) hL4
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hx0 : 0<x := zero_lt_one.trans hx
  have hn : 1 ≤ n := by
    change (1:ℝ) ≤ (giantTwoSidedSourceMomentLength x:ℝ)
    exact_mod_cast Nat.succ_le_of_lt (giantTwoSidedSourceMomentLength_pos hL0)
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlog' : Real.log L ≤ L^(1/100:ℝ) := by
    change ‖Real.log L‖ ≤ 1*‖L^(1/100:ℝ)‖ at hlog
    simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg hlog0,
      abs_of_nonneg (Real.rpow_nonneg hL0.le _)] using hlog
  have hnl : n*Real.log L ≤ 4*L^(53/100:ℝ) := by
    calc
      _ ≤ (4*L^(13/25:ℝ))*L^(1/100:ℝ) :=
        mul_le_mul (giantTwoSidedSourceMomentLength_le hL) hlog' hlog0 (by positivity)
      _ = _ := by rw [mul_assoc,← Real.rpow_add hL0];norm_num
  have hpower : L^((C+G)*n) ≤ Real.exp (4*(C+G)*L^(53/100:ℝ)) := by
    rw [Real.rpow_def_of_pos hL0]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hnl (add_nonneg hC hG)
    nlinarith only [hh]
  have hsecond : Real.exp (-γ*L/4)*L^((C+G)*n) ≤ 1/2 := by
    calc
      _ ≤ Real.exp (-γ*L/4)*x^(γ/8) :=
        mul_le_mul_of_nonneg_left (hpower.trans hsub) (Real.exp_nonneg _)
      _ = x^(-(γ/8)) := by
        rw [Real.rpow_def_of_pos hx0,Real.rpow_def_of_pos hx0,← Real.exp_add]
        congr 1
        dsimp only [L]
        ring
      _ ≤ _ := hdecay.le
  have hfirst : 2*L^(-n) ≤ 1/2 := by
    have he := Real.rpow_le_rpow_of_exponent_le hL (show -n ≤ (-1:ℝ) by linarith)
    have hi : L⁻¹ ≤ (1/4:ℝ) := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) hL4
    rw [Real.rpow_neg_one] at he
    linarith
  have hpoly : L^(-(C+G+1)*n)*L^(C*n)=L^(-G*n)*L^(-n) := by
    rw [← Real.rpow_add hL0,← Real.rpow_add hL0]
    congr 1
    ring
  have hweight : L^(-G*n)*L^((C+G)*n)=L^(C*n) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  change (2*L^(-(C+G+1)*n)+Real.exp (-γ*L/4))*L^(C*n) ≤ L^(-G*n)
  calc
    _ = 2*(L^(-(C+G+1)*n)*L^(C*n))+Real.exp (-γ*L/4)*L^(C*n) := by ring
    _ = 2*(L^(-G*n)*L^(-n))+Real.exp (-γ*L/4)*(L^(-G*n)*L^((C+G)*n)) := by
      rw [hpoly,hweight]
    _ = L^(-G*n)*(2*L^(-n)+Real.exp (-γ*L/4)*L^((C+G)*n)) := by ring
    _ ≤ L^(-G*n)*(1/2+1/2) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (Real.rpow_nonneg hL0.le _)
    _ = _ := by ring

end
end ArtinMatthews
