module

public import ArtinMatthews.MarkedPhysicalSelectedResidueCount


set_option backward.privateInPublic true
@[expose] public section

/-! The actual selected subsets and all their SL2 classes fit the .98
modulus budget. No abstract cardinality or chosen-modulus premise is used. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedPhysicalBandPrimes_card_exp {J : Type*} [Fintype J]
    (e : J → ℝ) {x : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ (1/5:ℝ)) :
    ((markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x)).card:ℝ) ≤ 
      Real.exp (2*(Real.log x)^(1/5:ℝ)) := by
  let N := ⌊Real.exp (2*(Real.log x)^(1/5:ℝ))⌋₊
  have hs : markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x)⊆Finset.Icc 1 N := by
    intro p hp
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_Icc.mpr ⟨(mem_markedLogPowerBand.mp hj).1.pos,
      (Nat.le_floor_iff (Real.exp_nonneg _)).mpr (markedRootArc_band_prime_le hlog (he j) hj)⟩
  have hc : (markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x)).card ≤ N := by
    simpa only [Nat.card_Icc,add_tsub_cancel_right] using Finset.card_le_card hs
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (Real.exp_nonneg _))

theorem markedPhysicalSelectedResidueCount_log_bound {J : Type*} [Fintype J]
    (e : J → ℝ) {x : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ (1/5:ℝ))
    (a : MarkedPhysicalLabelPath (fun j => markedLogPowerBand (e j) x)
      (markedPadSlots x) (markedMemoryMomentLength x)) :
    markedPhysicalSelectedResidueCount e x a (2*markedPhysicalBonferroniDepth x+1) ≤ 
      Real.exp ((64*(Fintype.card J:ℝ)+56)*(Real.log x)^(49/50:ℝ)) := by
  let k := 2*markedPhysicalBonferroniDepth x+1
  let P := markedPhysicalBandPrimes (fun j => markedLogPowerBand (e j) x) \
    markedPhysicalPathUsedPrimes Finset.univ a
  let t := (Real.log x)^(1/5:ℝ)
  let s := (Real.log x)^(19/25:ℝ)
  let u := (Real.log x)^(24/25:ℝ)
  have hL : 0<Real.log x := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hL.le _
  have hs1 : 1 ≤ s := Real.one_le_rpow hlog (by norm_num)
  have hst : s*t=u := by
    dsimp [s,t,u]
    rw [← Real.rpow_add hL]
    norm_num
  have htu : t ≤ u := Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hsu : s ≤ u := Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  have hk : (k:ℝ) ≤ 2*s+3 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ s from le_trans (by norm_num) hs1)
    dsimp only [k]
    push_cast
    change (markedPhysicalBonferroniDepth x:ℝ)<s+1 at hh
    linarith
  have hc : max 1 (P.card:ℝ) ≤ Real.exp (2*t) := by
    apply max_le (Real.one_le_exp (by positivity))
    exact (Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)).trans
      (markedPhysicalBandPrimes_card_exp e hlog he)
  have hpre : ((k+1:ℕ):ℝ) ≤ Real.exp (6*u) := by
    have hkp : ((k+1:ℕ):ℝ) ≤ 6*s := by push_cast; linarith
    exact (hkp.trans (mul_le_mul_of_nonneg_left hsu (by norm_num))).trans
      (by linarith [Real.add_one_le_exp (6*u)])
  have hpow : (max 1 (P.card:ℝ))^k ≤ Real.exp (10*u) := by
    calc
      _ ≤ (Real.exp (2*t))^k := pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hc k
      _ = Real.exp ((k:ℝ)*(2*t)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (10*u) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hk (show 0 ≤ 2*t by positivity)]
  have hcost : ((k+1:ℕ):ℝ)*(max 1 (P.card:ℝ))^k ≤ Real.exp (16*u) := by
    calc
      _ ≤ Real.exp (6*u)*Real.exp (10*u) := mul_le_mul hpre hpow (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hcount := markedPhysicalSelectedResidueCount_finite_bound e hlog he a k le_rfl
  calc
    _ ≤ Real.exp ((64*(Fintype.card J:ℝ)+40)*(Real.log x)^(49/50:ℝ))*
        (((k+1:ℕ):ℝ)*(max 1 (P.card:ℝ))^k) := by simpa only [mul_assoc] using hcount
    _ ≤ Real.exp ((64*(Fintype.card J:ℝ)+40)*(Real.log x)^(49/50:ℝ))*Real.exp (16*u) :=
      mul_le_mul_of_nonneg_left hcost (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hu : u ≤ (Real.log x)^(49/50:ℝ) := Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
      nlinarith

end
end ArtinMatthews
