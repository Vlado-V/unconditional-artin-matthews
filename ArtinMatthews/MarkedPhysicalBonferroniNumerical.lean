module

public import ArtinMatthews.MarkedPhysicalBonferroniModulus
public import ArtinMatthews.MarkedBonferroniTail
public import ArtinMatthews.MarkedRootGridBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The true .76 factorial truncation beats the .73 path/label budget
and every required logarithmic power at the actual .5 moment length. -/

noncomputable section
namespace ArtinMatthews
open Filter

theorem marked_exp_log_power_le_moment_log (b γ A : ℝ) (hb : 0 < b)
    (hγ : (1/2:ℝ) < γ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,Real.exp (-b*(Real.log x)^γ) ≤
      (Real.log x)^(-A*(markedMemoryMomentLength x:ℝ)) := by
  have hr : Tendsto (fun L : ℝ => (3*A)*(Real.log L/L^(γ-1/2))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((isLittleO_log_rpow_atTop (sub_pos.mpr hγ)).tendsto_div_nhds_zero).const_mul (3*A)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (hr.eventually (Iio_mem_nhds hb))] with x hL hsmall
  let L := Real.log x
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hs : 0 < L^(1/2:ℝ) := Real.rpow_pos_of_pos hLp _
  have hs1 : 1 ≤ L^(1/2:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hceil := Nat.ceil_lt_add_one (div_nonneg hs.le (by norm_num : (0:ℝ) ≤ 2))
  have hN : (markedMemoryMomentLength x:ℝ) ≤ 3*L^(1/2:ℝ) := by
    unfold markedMemoryMomentLength
    change ((2*⌈L^(1/2:ℝ)/2⌉₊:ℕ):ℝ) ≤ _
    push_cast
    linarith
  have hp : 0 < L^(γ-1/2) := Real.rpow_pos_of_pos hLp _
  have hratio : 3*A*Real.log L ≤ b*L^(γ-1/2) := by
    have hh : (3*A*Real.log L)/L^(γ-1/2) < b := by
      simpa only [div_eq_mul_inv,mul_assoc] using hsmall
    exact ((div_lt_iff₀ hp).mp hh).le
  have hpow : L^(γ-1/2)*L^(1/2:ℝ)=L^γ := by
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  have hscale := mul_le_mul_of_nonneg_right hratio hs.le
  rw [mul_assoc b,hpow] at hscale
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hmain : A*(markedMemoryMomentLength x:ℝ)*Real.log L ≤ b*L^γ := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hA) hlog0
    nlinarith
  conv_rhs => rw [Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem markedPhysicalBonferroni_factorial_budget (K B A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (B*(Real.log x)^(73/100:ℝ))*
        markedFactorialTail (K*((markedMemoryMomentLength x:ℝ)+1))
          (2*markedPhysicalBonferroniDepth x+1) ≤
      (Real.log x)^(-A*(markedMemoryMomentLength x:ℝ)) := by
  have hlim : Tendsto (fun L : ℝ => B*L^(-3/100:ℝ)+8*K*L^(-13/50:ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,add_zero,neg_div] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/100)).const_mul B).add
        ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<13/50)).const_mul (8*K))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    Real.tendsto_log_atTop.eventually (hlim.eventually (Iio_mem_nhds hlog2)),
    marked_exp_log_power_le_moment_log (Real.log 2) (19/25) A hlog2 (by norm_num) hA]
    with x hL hsmall htarget
  let L := Real.log x
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hhalf : 1 ≤ L^(1/2:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hceil := Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg hLp.le (1/2:ℝ)) (by norm_num : (0:ℝ) ≤ 2))
  have hN : (markedMemoryMomentLength x:ℝ)+1 ≤ 4*L^(1/2:ℝ) := by
    unfold markedMemoryMomentLength
    change ((2*⌈L^(1/2:ℝ)/2⌉₊:ℕ):ℝ)+1 ≤ _
    push_cast
    linarith
  have hdepth : 2*L^(19/25:ℝ) ≤ (2*markedPhysicalBonferroniDepth x+1:ℕ) := by
    have hh : L^(19/25:ℝ) ≤ (markedPhysicalBonferroniDepth x:ℝ) := Nat.le_ceil _
    push_cast
    linarith
  have hmass : 0 ≤ K*((markedMemoryMomentLength x:ℝ)+1) := by positivity
  have ht := markedFactorialTail_le_exp hmass (2*markedPhysicalBonferroniDepth x+1) hdepth
  have hr : B*L^(73/100:ℝ)+8*K*L^(1/2:ℝ) ≤ Real.log 2*L^(19/25:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hLp.le (19/25:ℝ))
    have h1 : L^(-3/100:ℝ)*L^(19/25:ℝ)=L^(73/100:ℝ) := by rw [← Real.rpow_add hLp]; congr 1; norm_num
    have h2 : L^(-13/50:ℝ)*L^(19/25:ℝ)=L^(1/2:ℝ) := by rw [← Real.rpow_add hLp]; congr 1; norm_num
    rw [add_mul,mul_assoc B,h1,mul_assoc (8*K),h2] at hh
    exact hh
  apply (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le).trans
  apply le_trans _ htarget
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp only [L] at hN hr
  have hh := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2*K by positivity)
  nlinarith

end ArtinMatthews
