module

public import ArtinMatthews.ShiftedABLSourceParameters


set_option backward.privateInPublic true
@[expose] public section

/-! The conductor and spectral cutoff for the actual source block in
(5.9). The radius bound comes from a nonempty signed frequency block
and the two truncated dual lengths. -/

noncomputable section

namespace ArtinMatthews

/-- The product `CMZnrs` in ABL Theorem 2.4. Here `R` denotes the
dyadic scale of its signed summation index. -/
def ablTheorem24SpectralParameter (C R Z : ℝ) (n r s : ℕ) : ℝ :=
  C * R * Z * n * r * s

/-- The spectral Bessel scale in ABL Theorem 2.4. -/
def ablTheorem24BesselScale (C R : ℝ) (n r s : ℕ) : ℝ :=
  Real.sqrt (R * n) / ((s : ℝ) * Real.sqrt r * C)

theorem shiftedABLSource_block_bounds
    {A ε CK CZ M T R K₁ K₂ : ℝ} {N F d m3 m4 k1 k2 : ℕ}
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hCK : 0 < CK) (hCZ : 1 ≤ CZ)
    (hscaleConst : 16*CK ≤ CZ^2) (hM : 1 ≤ M) (hT : 1 ≤ T) (hN : 0 < N)
    (hF : 0 < F) (hd : 0 < d) (hne : m3 ≠ m4)
    (hm1 : M ≤ ((d*m3 : ℕ) : ℝ)) (hm1' : ((d*m3 : ℕ) : ℝ) ≤ 2*M)
    (hm2 : M ≤ ((d*m4 : ℕ) : ℝ)) (hm2' : ((d*m4 : ℕ) : ℝ) ≤ 2*M)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hk1 : (k1 : ℝ) ≤ 2*K₁) (hk2 : (k2 : ℝ) ≤ 2*K₂)
    (hR : 1 ≤ R) (hρ : R ≤ ((shiftedABLDualFrequency m3 m4 k1 k2).natAbs : ℝ)) :
    let P := shiftedABLSourceParameter M T N
    let Q := circlePowerQ P A
    let Z₁ := CZ * shiftedABLSourceWPrime ε M T N
    let n := shiftedABLFirstIndex m3 m4
    let r := m3*m4
    let C := Q / (F : ℝ)
    let P' := ablTheorem24SpectralParameter C R Z₁ n r F
    (F : ℝ) ≤ Q →
    K₁ ≤ CK*P^ε*Q^2/(M*T) → K₂ ≤ CK*P^ε*Q^2/(M*T) →
    R ≤ 8*CK*(M/(d : ℝ))*P^ε*Q^2/(M*T) ∧
      1 ≤ C ∧ 1 ≤ Z₁ ∧ Z₁ ≤ 8*CZ*P^ε ∧
      ablTheorem24BesselScale C R n r F ≤ Z₁ ∧
      P' = Q*R*Z₁*n*r ∧ 1 ≤ P' ∧ P' ≤ (110592*CK*CZ)*P^(3*A+4+2*ε) := by
  intro P Q Z₁ n r C P' hFQ hcut₁ hcut₂
  let B := M/(d : ℝ)
  let W := shiftedABLSourceWPrime ε M T N
  have hP : 1 ≤ P := shiftedABLSourceParameter_one_le hM hT hN
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hH : 1 ≤ M*T := one_le_mul_of_one_le_of_one_le hM hT
  have hF0 : (0 : ℝ) < F := by exact_mod_cast hF
  have hF1 : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hB_le : B ≤ P := by
    calc
      _ ≤ M := div_le_self (zero_le_one.trans hM) hd1
      _ ≤ T*M := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hT (zero_le_one.trans hM)
      _ ≤ _ := by
        change T*M ≤ T*M*N
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hN1
          (mul_nonneg (zero_le_one.trans hT) (zero_le_one.trans hM))
  obtain ⟨hQ,hQup⟩ := shiftedABLSource_circleQ_bounds hP hA
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hpow : 1 ≤ P^ε := Real.one_le_rpow hP hε
  have hpW : P^ε ≤ W := (shiftedABLSourceWPrime_bounds (ε := ε) hM hT hN).1
  have hW1 : 1 ≤ W := hpow.trans hpW
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hWup : W ≤ 8*P^ε := (shiftedABLSourceWPrime_bounds (ε := ε) hM hT hN).2.2.le
  obtain ⟨hm3,hm4,hn,hr⟩ := shiftedABLSource_cofactor_bounds
    hM hd hne hm1 hm1' hm2 hm2'
  change (B ≤ (m3 : ℝ) ∧ (m3 : ℝ) ≤ 2*B) at hm3
  change (B ≤ (m4 : ℝ) ∧ (m4 : ℝ) ≤ 2*B) at hm4
  change (1 ≤ n ∧ (n : ℝ) ≤ 2*B) at hn
  change (B^2 ≤ (r : ℝ) ∧ (r : ℝ) ≤ 4*B^2) at hr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hr1 : (1 : ℝ) ≤ r := by
    have hm30 : (0 : ℝ) < m3 := hB0.trans_le hm3.1
    have hm40 : (0 : ℝ) < m4 := hB0.trans_le hm4.1
    have hm3n : 0 < m3 := by exact_mod_cast hm30
    have hm4n : 0 < m4 := by exact_mod_cast hm40
    exact_mod_cast (Nat.mul_pos hm3n hm4n)
  have hRup : R ≤ 8*CK*B*P^ε*Q^2/(M*T) := by
    calc
      _ ≤ 4*B*(K₁+K₂) := shiftedABLSource_dual_radius_le
        hB0.le hK₁ hK₂ hm3.2 hm4.2 hk1 hk2 hρ
      _ ≤ 4*B*(CK*P^ε*Q^2/(M*T)+CK*P^ε*Q^2/(M*T)) :=
        mul_le_mul_of_nonneg_left (add_le_add hcut₁ hcut₂) (by positivity)
      _ = _ := by ring
  have hC1 : 1 ≤ C := (one_le_div hF0).2 hFQ
  have hZ1 : 1 ≤ Z₁ := one_le_mul_of_one_le_of_one_le hCZ hW1
  have hZup : Z₁ ≤ 8*CZ*P^ε := by
    change CZ*W ≤ _
    calc
      _ ≤ CZ*(8*P^ε) := mul_le_mul_of_nonneg_left hWup (zero_le_one.trans hCZ)
      _ = _ := by ring
  have hX : ablTheorem24BesselScale C R n r F ≤ Z₁ := by
    have hdenom : (F : ℝ)*Real.sqrt (r : ℝ)*C = Real.sqrt (r : ℝ)*Q := by
      change (F : ℝ)*Real.sqrt (r : ℝ)*(Q/(F : ℝ)) = _
      field_simp [hF0.ne']
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    have hsqrt : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (zero_lt_one.trans_le hr1)
    have hratio : P^ε/(M*T) ≤ W^2 := by
      calc
        _ ≤ P^ε := div_le_self (zero_le_one.trans hpow) hH
        _ ≤ W := hpW
        _ ≤ W^2 := by
          simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hW1 hW0
    unfold ablTheorem24BesselScale
    rw [hdenom]
    apply (div_le_iff₀ (mul_pos hsqrt hQ0)).2
    apply Real.sqrt_le_iff.2
    refine ⟨mul_nonneg (zero_le_one.trans hZ1) (mul_nonneg hsqrt.le hQ0.le), ?_⟩
    calc
      R * (n : ℝ) ≤ (8*CK*B*P^ε*Q^2/(M*T))*(2*B) :=
        mul_le_mul hRup hn.2 (Nat.cast_nonneg _) (by positivity)
      _ = 16*CK*B^2*(P^ε/(M*T))*Q^2 := by ring
      _ ≤ CZ^2*(r : ℝ)*W^2*Q^2 := by
        gcongr
        exact hr.1
      _ = (Z₁*(Real.sqrt (r : ℝ)*Q))^2 := by
        change _ = (CZ*W*(Real.sqrt (r : ℝ)*Q))^2
        rw [mul_pow, mul_pow CZ W, mul_pow (Real.sqrt (r : ℝ)) Q, Real.sq_sqrt hr0]
        ring
  have hPeq : P' = Q*R*Z₁*n*r := by
    change (Q/(F : ℝ))*R*Z₁*n*r*F = _
    field_simp [hF0.ne']
  have hP'1 : 1 ≤ P' :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hC1 hR) hZ1) hn1) hr1) hF1
  have hQcube : Q^3 ≤ 216*P^(3*A) := by
    calc
      _ ≤ (6*P^A)^3 := pow_le_pow_left₀ hQ0.le hQup 3
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast (P^A) 3, ← Real.rpow_mul hP0.le]
        norm_num
        rw [mul_comm A 3]
  have hP4 : P^4 = P^(4 : ℝ) := (Real.rpow_natCast P 4).symm
  have hPeps2 : (P^ε)^2 = P^(2*ε) := by
    rw [← Real.rpow_natCast (P^ε) 2, ← Real.rpow_mul hP0.le]
    norm_num
    rw [mul_comm ε 2]
  refine ⟨hRup,hC1,hZ1,hZup,hX,hPeq,hP'1,?_⟩
  calc
    P' = Q*R*Z₁*n*r := hPeq
    _ ≤ Q*(8*CK*B*P^ε*Q^2/(M*T))*(8*CZ*P^ε)*(2*B)*(4*B^2) := by
      gcongr <;> first | exact hn.2 | exact hr.2
    _ = (512*CK*CZ)*B^4*(P^ε)^2*Q^3/(M*T) := by ring
    _ ≤ (512*CK*CZ)*B^4*(P^ε)^2*Q^3 := div_le_self (by positivity) hH
    _ ≤ (512*CK*CZ)*P^4*(P^ε)^2*(216*P^(3*A)) := by
      gcongr
    _ = (110592*CK*CZ)*(P^(3*A)*P^(4 : ℝ)*P^(2*ε)) := by
      rw [hP4, hPeps2]
      ring
    _ = _ := by rw [← Real.rpow_add hP0, ← Real.rpow_add hP0]

/-- Fix the circle exponent first. The two small exponents and the
implicit constant then work uniformly for every actual nonempty source
block, with the spectral cutoff `Z₁ (P')^δ`. -/
theorem shiftedABLSource_principal_loss_budget
    {A CK CZ ν cap : ℝ} (hA : 0 ≤ A) (hCK : 0 < CK) (hCZ : 1 ≤ CZ)
    (hscaleConst : 16*CK ≤ CZ^2) (hν : 0 < ν) (hcap : 0 < cap) :
    ∃ ε δ C₀ : ℝ, 0 < ε ∧ ε ≤ cap ∧ 0 < δ ∧ δ ≤ cap ∧ 0 < C₀ ∧
      ∀ (M T R K₁ K₂ : ℝ) (N F d m3 m4 k1 k2 : ℕ),
        1 ≤ M → 1 ≤ T → 0 < N → 0 < F → 0 < d → m3 ≠ m4 →
        M ≤ ((d*m3 : ℕ) : ℝ) → ((d*m3 : ℕ) : ℝ) ≤ 2*M →
        M ≤ ((d*m4 : ℕ) : ℝ) → ((d*m4 : ℕ) : ℝ) ≤ 2*M →
        0 ≤ K₁ → 0 ≤ K₂ → (k1 : ℝ) ≤ 2*K₁ → (k2 : ℝ) ≤ 2*K₂ →
        1 ≤ R → R ≤ ((shiftedABLDualFrequency m3 m4 k1 k2).natAbs : ℝ) →
        let P := shiftedABLSourceParameter M T N
        let Q := circlePowerQ P A
        let Z₁ := CZ * shiftedABLSourceWPrime ε M T N
        let n := shiftedABLFirstIndex m3 m4
        let r := m3*m4
        let C := Q / (F : ℝ)
        let P' := ablTheorem24SpectralParameter C R Z₁ n r F
        (F : ℝ) ≤ Q →
        K₁ ≤ CK*P^ε*Q^2/(M*T) → K₂ ≤ CK*P^ε*Q^2/(M*T) →
        1 ≤ Z₁ * (P')^δ ∧ Real.sqrt (Z₁ * (P')^δ) ≤ C₀*P^ν := by
  let E := 3*A+6
  let D := 110592*CK*CZ
  let ε := min 1 (min cap (ν/2))
  let δ := min cap (ν/(E+1))
  have hE : 0 ≤ E := by dsimp [E]; linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hε : 0 < ε := lt_min (by norm_num) (lt_min hcap (by positivity))
  have hεcap : ε ≤ cap := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεν : ε ≤ ν/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hE1 : 0 < E+1 := by linarith
  have hδ : 0 < δ := lt_min hcap (div_pos hν hE1)
  have hδcap : δ ≤ cap := min_le_left _ _
  have hEδ : E*δ ≤ ν := by
    have h := (le_div_iff₀ hE1).1 (min_le_right cap (ν/(E+1)))
    change δ*(E+1) ≤ ν at h
    linarith [hδ.le]
  have hbudget : (ε+E*δ)/2 ≤ ν := by linarith
  let C₀ := Real.sqrt (8*CZ*D^δ)
  have hC₀ : 0 < C₀ := Real.sqrt_pos.2 (by positivity)
  refine ⟨ε,δ,C₀,hε,hεcap,hδ,hδcap,hC₀,?_⟩
  intro M T R K₁ K₂ N F d m3 m4 k1 k2 hM hT hN hF hd hne
    hm1 hm1' hm2 hm2' hK₁ hK₂ hk1 hk2 hR hρ P Q Z₁ n r C P' hFQ hcut₁ hcut₂
  obtain ⟨_,_,hZ1,hZup,_,_,hP'1,hP'up⟩ :=
    shiftedABLSource_block_bounds hA hε.le hCK hCZ hscaleConst hM hT hN hF hd hne
      hm1 hm1' hm2 hm2' hK₁ hK₂ hk1 hk2 hR hρ hFQ hcut₁ hcut₂
  have hP : 1 ≤ P := shiftedABLSourceParameter_one_le hM hT hN
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hP' : P' ≤ D*P^E :=
    hP'up.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP (by dsimp [E]; linarith)) hD.le)
  refine ⟨one_le_mul_of_one_le_of_one_le hZ1 (Real.one_le_rpow hP'1 hδ.le), ?_⟩
  have hmul : Z₁*(P')^δ ≤ (8*CZ*D^δ)*P^(ε+E*δ) := by
    calc
      _ ≤ (8*CZ*P^ε)*(D*P^E)^δ :=
        mul_le_mul hZup (Real.rpow_le_rpow (zero_le_one.trans hP'1) hP' hδ.le)
          (Real.rpow_nonneg (zero_le_one.trans hP'1) _) (by positivity)
      _ = _ := by
        rw [Real.mul_rpow hD.le (Real.rpow_nonneg hP0.le _),
          ← Real.rpow_mul hP0.le, Real.rpow_add hP0]
        ring
  calc
    _ ≤ Real.sqrt ((8*CZ*D^δ)*P^(ε+E*δ)) := Real.sqrt_le_sqrt hmul
    _ = C₀*P^((ε+E*δ)/2) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 8*CZ*D^δ),
        Real.sqrt_eq_rpow (P^(ε+E*δ)), ← Real.rpow_mul hP0.le]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hbudget) hC₀.le

end ArtinMatthews
