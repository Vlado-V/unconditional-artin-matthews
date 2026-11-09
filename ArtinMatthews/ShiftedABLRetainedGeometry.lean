module

public import ArtinMatthews.ShiftedABLBesselConditionBudget
public import ArtinMatthews.ShiftedABLThetaSignedReassembly
public import ArtinMatthews.ShiftedABLOriginalParameters


set_option backward.privateInPublic true
@[expose] public section

/-! The exact retained signed blocks satisfy all source Bessel and
spectral parameter bounds, with the original circle cutoff. -/
namespace ArtinMatthews
noncomputable section

theorem shiftedABL_retained_block_parameter_bounds
    {A ε M T : ℝ} {N m1 m2 : ℕ}
    (hA : 12 ≤ A) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hM : 1 ≤ M) (hT : 1 ≤ T) (hN : 2 ≤ N)
    (hm1 : M ≤ (m1 : ℝ)) (hm1' : (m1 : ℝ) ≤ 2*M)
    (hm2 : M ≤ (m2 : ℝ)) (hm2' : (m2 : ℝ) ≤ 2*M)
    (hne : m1 ≠ m2) (hs1 : Squarefree m1) (hs2 : Squarefree m2)
    (hcop : N.Coprime (m1*m2)) :
    let P := shiftedABLSourceParameter M T N
    let Q := circlePowerQ P A
    let U := shiftedABLThetaDualCutoff M T P Q ε
    let J := shiftedABLDualCutoffIndex U
    let d0 := m1.gcd m2
    let D := shiftedCommonPrimePart m1 m2
    let m3 := m1/d0
    let m4 := m2/d0
    let F := N*D^2
    let r := m3*m4
    let n := shiftedABLFirstIndex m3 m4
    let g := (r*F).gcd n
    ∀ d ∈ shiftedABLDualRectangle J, ∀ i ∈ shiftedABLSignedFrequencyIndices m3 m4 d,
      let R := (2:ℝ)^i.1
      let K1 := (2:ℝ)^d.1
      let K2 := (2:ℝ)^d.2
      let X := Real.sqrt (R*(n:ℝ))/(Real.sqrt (r:ℝ)*Q)
      let V := 16*Real.sqrt (P^ε)
      let G := Real.sqrt ((n:ℝ)*(g:ℝ))
      let P0 := Q*R*(n:ℝ)*(r:ℝ)
      K1 ≤ 8*P^ε*Q^2/(M*T) ∧ K2 ≤ 8*P^ε*Q^2/(M*T) ∧
      1 ≤ R ∧ R ≤ 64*(M/(d0:ℝ))*P^ε*Q^2/(M*T) ∧
      0 < X ∧ X ≤ 16*(N:ℝ) ∧ 1 ≤ V ∧ (n:ℝ)*X ≤ V*G ∧
      Real.sqrt V ≤ 4*P^ε ∧ P0 ≤ (110592*8*16)*P^(3*A+6) := by
  intro P Q U J d0 D m3 m4 F r n g d hd i hi R K1 K2 X V G P0
  have hA0 : 0 ≤ A := by linarith
  have hH : 1 ≤ M*T := one_le_mul_of_one_le_of_one_le hM hT
  have hH0 : 0 < M*T := zero_lt_one.trans_le hH
  have hN0 : 0 < N := by omega
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hN0)
  have hm10 : 0 < m1 := by exact_mod_cast (zero_lt_one.trans_le (hM.trans hm1))
  have hm20 : 0 < m2 := by exact_mod_cast (zero_lt_one.trans_le (hM.trans hm2))
  obtain ⟨hd0,_,_,_,hm34,hfactor1,hfactor2,_,_,_,hF,hr,_⟩ :=
    shiftedABLOriginal_cofactors hN0 hm10 hm20 hne hs1 hs2 hcop
  obtain ⟨hP2,hHP,_,_,_,_,_,_,hFup,_⟩ :=
    shiftedABLOriginal_scale_bounds hM hT hN hm1 hm1' hm2 hm2' hne hs1 hs2 hcop
  have hP1 : 1 ≤ P := (by norm_num : (1:ℝ) ≤ 2).trans hP2
  obtain ⟨hQ1,_⟩ := shiftedABLSource_circleQ_bounds hP1 hA0
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  have hPA : P ≤ P^A := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hP1 (show (1:ℝ) ≤ A by linarith))
  have hHQ : M*T ≤ Q := hHP.trans (hPA.trans circlePowerQ_lower)
  have hFQ : (F:ℝ) ≤ Q := hFup.trans
    ((Real.rpow_le_rpow_of_exponent_le hP1 (show (5:ℝ) ≤ A by linarith)).trans circlePowerQ_lower)
  have hU1 : 1 ≤ U := by
    change 1 ≤ (4*Q^2/(M*T))*P^ε
    have hQsq : Q ≤ Q^2 := by
      simpa only [one_mul,pow_two] using mul_le_mul_of_nonneg_right hQ1 hQ0.le
    have hpre : 1 ≤ 4*Q^2/(M*T) := (le_div_iff₀ hH0).mpr (by nlinarith only [hHQ,hQsq,sq_nonneg Q])
    exact one_le_mul_of_one_le_of_one_le hpre (Real.one_le_rpow hP1 hε)
  obtain ⟨ρ,hρ,hρi⟩ := Finset.mem_image.mp hi
  have hfilter : ρ ∈ (shiftedABLDualFrequencies m3 m4 d).filter
      (fun ρ => shiftedABLSignedFrequencyIndex ρ = i) := Finset.mem_filter.mpr ⟨hρ,hρi⟩
  obtain ⟨hK1,hK2,hR,k1,k2,hk1,hk2,hfreq⟩ := shiftedABLThetaSignedBlock_geometry
    (shiftedABLDualCutoffIndex_bounds hU1).2 hd hfilter
  have hcut : 2*U = 8*P^ε*Q^2/(M*T) := by
    dsimp only [U,shiftedABLThetaDualCutoff]
    ring
  have hcut1 : K1 ≤ 8*P^ε*Q^2/(M*T) := hK1.trans_eq hcut
  have hcut2 : K2 ≤ 8*P^ε*Q^2/(M*T) := hK2.trans_eq hcut
  have hR1 : 1 ≤ R := hR.1
  have hRfreq : R ≤ ((shiftedABLDualFrequency m3 m4 k1 k2).natAbs : ℝ) := by
    rw [hfreq]
    exact hR.2.1
  change d0*m3=m1 at hfactor1
  change d0*m4=m2 at hfactor2
  have hm1a : M ≤ ((d0*m3:ℕ):ℝ) := by simpa only [hfactor1] using hm1
  have hm1b : ((d0*m3:ℕ):ℝ) ≤ 2*M := by simpa only [hfactor1] using hm1'
  have hm2a : M ≤ ((d0*m4:ℕ):ℝ) := by simpa only [hfactor2] using hm2
  have hm2b : ((d0*m4:ℕ):ℝ) ≤ 2*M := by simpa only [hfactor2] using hm2'
  obtain ⟨hRup,_,hZ1,_,_,hPeq,_,hPbig⟩ := shiftedABLSource_block_bounds
    (A := A) (ε := ε) (CK := 8) (CZ := 16) (T := T) (R := R) (K₁ := K1) (K₂ := K2)
    (N := N) (F := F) (d := d0) hA0 hε (by norm_num) (by norm_num) (by norm_num)
    hM hT hN0 hF hd0 hm34 hm1a hm1b hm2a hm2b (by dsimp [K1]; positivity)
    (by dsimp [K2]; positivity) hk1 hk2 hR1 hRfreq hFQ hcut1 hcut2
  have hRup' : R ≤ 64*(M/(d0:ℝ))*P^ε*Q^2/(M*T) := by
    simpa only [show (8:ℝ)*8=64 by norm_num] using hRup
  let B := M/(d0:ℝ)
  have hd01 : (1:ℝ) ≤ d0 := by exact_mod_cast (Nat.succ_le_of_lt hd0)
  have hB0 : 0 < B := div_pos (zero_lt_one.trans_le hM) (zero_lt_one.trans_le hd01)
  have hBH : B ≤ M*T := (div_le_self (zero_le_one.trans hM) hd01).trans
    (le_mul_of_one_le_right (zero_le_one.trans hM) hT)
  obtain ⟨_,_,hnB,hrB⟩ := shiftedABLSource_cofactor_bounds hM hd0 hm34 hm1a hm1b hm2a hm2b
  have hn0 : 0 < n := zero_lt_one.trans_le hnB.1
  have hnH : (n:ℝ) ≤ 2*(M*T) := hnB.2.trans (mul_le_mul_of_nonneg_left hBH (by norm_num))
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right (r*F) n) hn0
  have hg1 : (1:ℝ) ≤ g := by exact_mod_cast (Nat.succ_le_of_lt hg0)
  have hPdef : P = (N:ℝ)*(M*T) := by dsimp only [P,shiftedABLSourceParameter]; ring
  obtain ⟨hX0,hXup,hV1,hnX,hVup⟩ := shiftedABL_source_bessel_conditions
    (H := M*T) (B := B) (Q := Q) (r := (r:ℝ)) (n := (n:ℝ)) (R := R)
    (P := P) (N := (N:ℝ)) (g := (g:ℝ))
    hH0 hB0 hQ0 (by exact_mod_cast hr) (by exact_mod_cast hn0) (zero_lt_one.trans_le hR1)
    hP1 hN1 hg1 hε hε1 hPdef hRup' hrB.1 hnB.2 hnH
  let Z1 := 16*shiftedABLSourceWPrime ε M T N
  have hP0up : P0 ≤ (110592*8*16)*P^(3*A+6) := by
    calc
      P0 = (Q*R*1)*(n:ℝ)*(r:ℝ) := by simp only [P0,mul_one]
      _ ≤ Q*R*Z1*(n:ℝ)*(r:ℝ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZ1
          (mul_nonneg hQ0.le (zero_le_one.trans hR1))) (Nat.cast_nonneg n)) (Nat.cast_nonneg r)
      _ = ablTheorem24SpectralParameter (Q/(F:ℝ)) R Z1 n r F := hPeq.symm
      _ ≤ (110592*8*16)*P^(3*A+4+2*ε) := hPbig
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)) (by norm_num)
  exact ⟨hcut1,hcut2,hR1,hRup',hX0,hXup,hV1,hnX,hVup,hP0up⟩

end
end ArtinMatthews
