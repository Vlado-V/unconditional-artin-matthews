module

public import ArtinMatthews.ShiftedABLSourceBudget
public import ArtinMatthews.ShiftedCommonPrimePartSquarefree


set_option backward.privateInPublic true
@[expose] public section

/-! The actual gcd quotients, full common-prime part and detector
parameters of the squarefree shifted source. -/

noncomputable section
namespace ArtinMatthews

theorem shiftedABLOriginal_cofactors {N m1 m2 : ℕ}
    (hN : 0 < N) (hm1 : 0 < m1) (hm2 : 0 < m2) (hne : m1 ≠ m2)
    (hs1 : Squarefree m1) (hs2 : Squarefree m2) (hcop : N.Coprime (m1*m2)) :
    let d := m1.gcd m2
    let D := shiftedCommonPrimePart m1 m2
    let m3 := m1/d
    let m4 := m2/d
    let F := N*D^2
    let r := m3*m4
    0 < d ∧ 0 < D ∧ 0 < m3 ∧ 0 < m4 ∧ m3 ≠ m4 ∧
      d*m3=m1 ∧ d*m4=m2 ∧ m3 ≤ m1 ∧ m4 ≤ m2 ∧
      D ≤ ((m1 : ℤ)-m2).natAbs ∧ 0 < F ∧ 0 < r ∧ F.Coprime r := by
  intro d D m3 m4 F r
  have hd : 0 < d := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m1 m2) hm1
  have h1 : d*m3=m1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left m1 m2)
  have h2 : d*m4=m2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right m1 m2)
  have hm3 : 0 < m3 := Nat.pos_of_mul_pos_left (show 0 < d*m3 by simpa only [h1] using hm1)
  have hm4 : 0 < m4 := Nat.pos_of_mul_pos_left (show 0 < d*m4 by simpa only [h2] using hm2)
  have hneq : m3 ≠ m4 := by intro h; apply hne; rw [← h1,← h2,h]
  have hn : ((m1 : ℤ)-m2).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
  have hD : 0 < D := Nat.pos_of_ne_zero (commonPrimePart_ne_zero hn d)
  have hDle : D ≤ ((m1 : ℤ)-m2).natAbs :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (commonPrimePart_dvd _ d)
  obtain ⟨_,_,_,_,_,_,hdcop,_⟩ := squarefree_commonPrimePart_factors hm1 hm2 hne hs1 hs2
  have hDr : D.Coprime r := commonPrimePart_coprime hn hdcop
  have hdiv1 : m3 ∣ m1 := ⟨d, by rw [←h1]; ring⟩
  have hdiv2 : m4 ∣ m2 := ⟨d, by rw [←h2]; ring⟩
  have hNr : N.Coprime r := hcop.of_dvd_right (Nat.mul_dvd_mul hdiv1 hdiv2)
  exact ⟨hd,hD,hm3,hm4,hneq,h1,h2,Nat.div_le_self _ _,Nat.div_le_self _ _,
    hDle,Nat.mul_pos hN (pow_pos hD _),Nat.mul_pos hm3 hm4,hNr.mul_left (hDr.pow_left 2)⟩

theorem shiftedABLOriginal_scale_bounds {M T : ℝ} {N m1 m2 : ℕ}
    (hM : 1 ≤ M) (hT : 1 ≤ T) (hN : 2 ≤ N)
    (hm1 : M ≤ (m1 : ℝ)) (hm1' : (m1 : ℝ) ≤ 2*M)
    (hm2 : M ≤ (m2 : ℝ)) (hm2' : (m2 : ℝ) ≤ 2*M)
    (hne : m1 ≠ m2) (hs1 : Squarefree m1) (hs2 : Squarefree m2)
    (hcop : N.Coprime (m1*m2)) :
    let P := shiftedABLSourceParameter M T N
    let d := m1.gcd m2
    let D := shiftedCommonPrimePart m1 m2
    let m3 := m1/d
    let m4 := m2/d
    let F := N*D^2
    let r := m3*m4
    2 ≤ P ∧ M*T ≤ P ∧ M ≤ P ∧ (N : ℝ) ≤ P ∧
      (D : ℝ) ≤ 2*P ∧ (m3 : ℝ) ≤ 2*P ∧ (m4 : ℝ) ≤ 2*P ∧
      (shiftedABLFirstIndex m3 m4 : ℝ) ≤ 2*P ∧
      (F : ℝ) ≤ P^(5 : ℝ) ∧ (r : ℝ) ≤ P^(5 : ℝ) := by
  intro P d D m3 m4 F r
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 0 < m1 := by exact_mod_cast hM0.trans_le hm1
  have h2 : 0 < m2 := by exact_mod_cast hM0.trans_le hm2
  obtain ⟨hd,hD,hm3,hm4,hneq,hfactor1,hfactor2,h3le,h4le,hDle,hF,hr,hFr⟩ :=
    shiftedABLOriginal_cofactors (by omega : 0 < N) h1 h2 hne hs1 hs2 hcop
  have hH : 1 ≤ M*T := one_le_mul_of_one_le_of_one_le hM hT
  have hHP : M*T ≤ P := by
    change M*T ≤ T*M*N
    nlinarith [mul_le_mul_of_nonneg_left hN1 (mul_nonneg hT0.le hM0.le)]
  have hMP : M ≤ P := (by nlinarith [mul_le_mul_of_nonneg_left hT hM0.le] : M ≤ M*T).trans hHP
  have hNP : (N : ℝ) ≤ P := by
    change (N : ℝ) ≤ T*M*N
    nlinarith [mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hP : 2 ≤ P := hN2.trans hNP
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hD2 : (D : ℝ) ≤ 2*M := by
    have hnat : ((m1 : ℤ)-m2).natAbs ≤ max m1 m2 := by
      exact Int.natAbs_coe_sub_coe_le_of_le (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hmax : ((max m1 m2 : ℕ) : ℝ) ≤ 2*M := by
      simpa only [Nat.cast_max] using max_le hm1' hm2'
    exact (Nat.cast_le.mpr (hDle.trans hnat)).trans hmax
  have hDupper := hD2.trans (by linarith : 2*M ≤ 2*P)
  have hm3upper : (m3 : ℝ) ≤ 2*P :=
    (Nat.cast_le.mpr h3le).trans (hm1'.trans (by linarith))
  have hm4upper : (m4 : ℝ) ≤ 2*P :=
    (Nat.cast_le.mpr h4le).trans (hm2'.trans (by linarith))
  have hnupper : (shiftedABLFirstIndex m3 m4 : ℝ) ≤ 2*P := by
    have he : (shiftedABLFirstIndex m3 m4 : ℝ) = |(m3 : ℝ)-m4| := by
      simp [shiftedABLFirstIndex,Nat.cast_natAbs]
    rw [he]
    exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) m3],
      by linarith [Nat.cast_nonneg (α := ℝ) m4]⟩
  have hfour : (4 : ℝ) ≤ P^2 := by nlinarith
  have hFup : (F : ℝ) ≤ P^(5 : ℝ) := by
    change ((N*D^2 : ℕ) : ℝ) ≤ _
    push_cast
    calc
      _ ≤ P*(2*P)^2 := by gcongr
      _ = 4*P^3 := by ring
      _ ≤ P^2*P^3 := mul_le_mul_of_nonneg_right hfour (by positivity)
      _ = P^(5 : ℝ) := by norm_num [Real.rpow_natCast]; ring
  have hrup : (r : ℝ) ≤ P^(5 : ℝ) := by
    change ((m3*m4 : ℕ) : ℝ) ≤ _
    push_cast
    calc
      _ ≤ (2*P)*(2*P) := by gcongr
      _ = 4*P^2 := by ring
      _ ≤ P^2*P^2 := mul_le_mul_of_nonneg_right hfour (by positivity)
      _ = P^(4 : ℝ) := by norm_num [Real.rpow_natCast]; ring
      _ ≤ P^(5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
  exact ⟨hP,hHP,hMP,hNP,hDupper,hm3upper,hm4upper,hnupper,hFup,hrup⟩

theorem shiftedABLOriginal_detector_threshold {M T A : ℝ} {N m1 m2 : ℕ}
    (hM : 1 ≤ M) (hT : 1 ≤ T) (hN : 2 ≤ N) (hA : 12 ≤ A)
    (hm1 : M ≤ (m1 : ℝ)) (hm1' : (m1 : ℝ) ≤ 2*M)
    (hm2 : M ≤ (m2 : ℝ)) (hm2' : (m2 : ℝ) ≤ 2*M)
    (hne : m1 ≠ m2) (hs1 : Squarefree m1) (hs2 : Squarefree m2)
    (hcop : N.Coprime (m1*m2)) :
    let P := shiftedABLSourceParameter M T N
    let D := shiftedCommonPrimePart m1 m2
    let r := (m1/m1.gcd m2)*(m2/m1.gcd m2)
    4*((N*D^2)*r) ≤ circlePowerScale P A := by
  obtain ⟨hP,_,_,_,_,_,_,_,hF,hr⟩ :=
    shiftedABLOriginal_scale_bounds hM hT hN hm1 hm1' hm2 hm2' hne hs1 hs2 hcop
  exact circlePowerScale_threshold hP (by norm_num : (0 : ℝ) ≤ 5)
    (by linarith : 2*(5 : ℝ)+2 ≤ A) hF hr

end ArtinMatthews
