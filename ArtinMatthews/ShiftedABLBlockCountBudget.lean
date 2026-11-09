module

public import ArtinMatthews.ShiftedABLThetaSignedReassembly
public import ArtinMatthews.CircleParameterBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite signed/dyadic block count costs an arbitrarily
small source power after the circle exponent has been fixed. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

private theorem dyadic_index_power_bound (D b ν : ℝ)
    (hD : 1 ≤ D) (hb : 0 ≤ b) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ j : ℕ,
      (2 : ℝ)^j ≤ D*P^b → (j : ℝ)+1 ≤ C*P^ν := by
  let C := (Real.log D+b/ν)/Real.log 2+1
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro P hP j hj
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hpow : 1 ≤ P^ν := Real.one_le_rpow hP1 hν.le
  have hlog := Real.log_le_log (show 0 < (2 : ℝ)^j by positivity) hj
  rw [Real.log_pow,Real.log_mul (show D ≠ 0 by linarith)
    (Real.rpow_pos_of_pos hP0 b).ne',Real.log_rpow hP0] at hlog
  have hbound : (j : ℝ)*Real.log 2 ≤ (Real.log D+b/ν)*P^ν := by
    calc
      _ ≤ Real.log D+b*Real.log P := hlog
      _ ≤ Real.log D*P^ν+b*(P^ν/ν) := add_le_add
        (le_mul_of_one_le_right hlogD hpow)
        (mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hP0.le hν) hb)
      _ = _ := by ring
  have hidx : (j : ℝ) ≤ ((Real.log D+b/ν)/Real.log 2)*P^ν := by
    have hh : (j : ℝ) ≤ ((Real.log D+b/ν)*P^ν)/Real.log 2 :=
      (le_div_iff₀ hlog2).mpr hbound
    exact hh.trans_eq (by ring)
  dsimp [C]
  nlinarith only [hidx,hpow]

theorem shiftedABLThetaSignedBlock_count_power_budget {A ε ν : ℝ}
    (hA : 1 ≤ A) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M T : ℝ) (N m1 m2 : ℕ),
      1 ≤ M → 1 ≤ T → 2 ≤ N → (m1 : ℝ) ≤ 2*M → (m2 : ℝ) ≤ 2*M →
      let P := shiftedABLSourceParameter M T N
      let Q := circlePowerQ P A
      let U := shiftedABLThetaDualCutoff M T P Q ε
      let J := shiftedABLDualCutoffIndex U
      let m3 := m1/(m1.gcd m2)
      let m4 := m2/(m1.gcd m2)
      ((∑ d ∈ shiftedABLDualRectangle J,
        (shiftedABLSignedFrequencyIndices m3 m4 d).card : ℕ) : ℝ) ≤ C*P^ν := by
  let δ := ν/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C1,hC1,hindex1⟩ := dyadic_index_power_bound 288 (2*A+1) δ
    (by norm_num) (by linarith) hδ
  obtain ⟨C2,hC2,hindex2⟩ := dyadic_index_power_bound 2304 (2*A+2) δ
    (by norm_num) (by linarith) hδ
  refine ⟨2*C1^2*C2,by positivity,?_⟩
  intro M T N m1 m2 hM hT hN hm1 hm2 P Q U J m3 m4
  let H := M*T
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hM hT
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hP2 : 2 ≤ P := by
    have hproduct : 1 ≤ T*M := by simpa only [H,mul_comm] using hH
    have hh := mul_le_mul_of_nonneg_right hproduct (Nat.cast_nonneg (α := ℝ) N)
    change 2 ≤ T*M*N
    nlinarith only [hNR,hh]
  have hP1 : 1 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  have hHP : H ≤ P := by
    calc
      H ≤ H*N := le_mul_of_one_le_right hH0.le (by linarith : (1 : ℝ) ≤ N)
      _ = P := by dsimp [H,P,shiftedABLSourceParameter]; ring
  have hMP : M ≤ P := (by nlinarith [mul_le_mul_of_nonneg_left hT (by linarith : 0 ≤ M)] : M ≤ H).trans hHP
  obtain ⟨hQ1,hQup⟩ := shiftedABLSource_circleQ_bounds hP1 (by linarith : 0 ≤ A)
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  have hHQ : H ≤ Q := hHP.trans
    ((by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP1 hA : P ≤ P^A).trans
      circlePowerQ_lower)
  have hU1 : 1 ≤ U := by
    have hs : 1 ≤ 4*Q^2/H := (le_div_iff₀ hH0).mpr (by nlinarith only [hHQ,hQ1])
    exact one_le_mul_of_one_le_of_one_le hs (Real.one_le_rpow hP1 hε)
  have hPε : P^ε ≤ P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP1 hε1
  have hpower : (P^A)^2 = P^(2*A) := by
    rw [← Real.rpow_natCast (P^A) 2,← Real.rpow_mul hP0.le]
    congr 1
    norm_num
    ring
  have hUup : U ≤ 144*P^(2*A+1) := by
    calc
      U = (4*Q^2/H)*P^ε := rfl
      _ ≤ (4*Q^2)*P^ε := mul_le_mul_of_nonneg_right
        (div_le_self (by positivity) hH) (Real.rpow_nonneg hP0.le _)
      _ ≤ (4*(6*P^A)^2)*P := by gcongr
      _ = 144*P^(2*A+1) := by rw [mul_pow,hpower,Real.rpow_add hP0,Real.rpow_one]; norm_num; ring
  have hJpow : (2 : ℝ)^J ≤ 288*P^(2*A+1) :=
    (shiftedABLDualCutoffIndex_bounds hU1).2.trans (by linarith)
  have hJ := hindex1 P hP2 J hJpow
  let Z := (m3+m4)*(2*2^J)
  have hsum : ((m3+m4 : ℕ) : ℝ) ≤ 4*P := by
    have hm3 : (m3 : ℝ) ≤ (m1 : ℝ) := Nat.cast_le.mpr (Nat.div_le_self _ _)
    have hm4 : (m4 : ℝ) ≤ (m2 : ℝ) := Nat.cast_le.mpr (Nat.div_le_self _ _)
    push_cast
    linarith
  push_cast at hsum
  have hZ : (Z : ℝ) ≤ 2304*P^(2*A+2) := by
    change (((m3+m4)*(2*2^J) : ℕ) : ℝ) ≤ _
    push_cast
    calc
      _ ≤ (4*P)*(2*(288*P^(2*A+1))) := by gcongr
      _ = 2304*P^(2*A+2) := by
        have he : P*P^(2*A+1)=P^(2*A+2) := by
          calc
            _ = P^((1 : ℝ)+(2*A+1)) := by
              simpa only [Real.rpow_one] using (Real.rpow_add hP0 1 (2*A+1)).symm
            _ = _ := by congr 1; ring
        calc
          _ = 2304*(P*P^(2*A+1)) := by ring
          _ = _ := by rw [he]
  have hZpow : (2 : ℝ)^(Nat.log 2 Z) ≤ 2304*P^(2*A+2) := by
    by_cases hz : Z=0
    · simp only [hz,Nat.log_zero_right,pow_zero]
      have := Real.one_le_rpow hP1 (show 0 ≤ 2*A+2 by linarith)
      nlinarith
    · have hsmall : (2 : ℝ)^(Nat.log 2 Z) ≤ (Z : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hz
      exact hsmall.trans hZ
  have hZindex := hindex2 P hP2 (Nat.log 2 Z) hZpow
  have hcount : ((∑ d ∈ shiftedABLDualRectangle J,
      (shiftedABLSignedFrequencyIndices m3 m4 d).card : ℕ) : ℝ) ≤
        ((J : ℝ)+1)^2*((((Nat.log 2 Z : ℕ) : ℝ)+1)*2) := by
    have h := shiftedABLThetaSignedBlock_count_le J m3 m4
    exact_mod_cast h
  have hcube : (P^δ)^2*(P^δ)=P^ν := by
    rw [← pow_succ,← Real.rpow_natCast (P^δ) 3,← Real.rpow_mul hP0.le]
    congr 1
    dsimp [δ]
    ring
  calc
    _ ≤ ((J : ℝ)+1)^2*((((Nat.log 2 Z : ℕ) : ℝ)+1)*2) := hcount
    _ ≤ (C1*P^δ)^2*((C2*P^δ)*2) := by gcongr
    _ = (2*C1^2*C2)*((P^δ)^2*(P^δ)) := by ring
    _ = _ := by rw [hcube]

end ArtinMatthews
