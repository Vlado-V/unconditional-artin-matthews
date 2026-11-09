module

public import ArtinMatthews.ShiftedABLOriginalParameters
public import ArtinMatthews.CircleThetaErrorRate
public import ArtinMatthews.ShiftedSourceCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Actual source cutoff sizes and the quantitative finite-detector error
at a fixed circle power. -/

noncomputable section
open Set

namespace ArtinMatthews

theorem shiftedABLOriginal_sourceCutoffs {M T P : ℝ} {m1 m2 : ℕ}
    (hP : 1 ≤ P) (hH : M*T ≤ P) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hm1 : (m1 : ℝ) ≤ 2*M) (hm2 : (m2 : ℝ) ≤ 2*M)
    (hMP : M ≤ P) :
    let T1 := ⌈1+2*(m1 : ℝ)*T⌉₊
    let T2 := ⌈1+5*(m2 : ℝ)*T/2⌉₊
    (T1 : ℝ) ≤ 8*P ∧ (T2 : ℝ) ≤ 8*P ∧
      ((((m2/(m1.gcd m2))*T1+(m1/(m1.gcd m2))*T2 : ℕ) : ℝ)) ≤ 32*P^2 := by
  intro T1 T2
  have hm1T : (m1 : ℝ)*T ≤ 2*P := by nlinarith [mul_le_mul_of_nonneg_right hm1 hT]
  have hm2T : (m2 : ℝ)*T ≤ 2*P := by nlinarith [mul_le_mul_of_nonneg_right hm2 hT]
  have hT1 : (T1 : ℝ) ≤ 8*P := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 1+2*(m1 : ℝ)*T by positivity)
    change (⌈1+2*(m1 : ℝ)*T⌉₊ : ℝ) ≤ _
    linarith
  have hT2 : (T2 : ℝ) ≤ 8*P := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 1+5*(m2 : ℝ)*T/2 by positivity)
    change (⌈1+5*(m2 : ℝ)*T/2⌉₊ : ℝ) ≤ _
    linarith
  refine ⟨hT1,hT2,?_⟩
  have hd1 : ((m1/(m1.gcd m2) : ℕ) : ℝ) ≤ 2*P :=
    (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (hm1.trans (by linarith))
  have hd2 : ((m2/(m1.gcd m2) : ℕ) : ℝ) ≤ 2*P :=
    (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans (hm2.trans (by linarith))
  push_cast
  calc
    _ ≤ (2*P)*(8*P)+(2*P)*(8*P) := by gcongr
    _ = _ := by ring

theorem shiftedABLOriginal_detector_error
    {A E : ℝ} (hA : 12 ≤ A) (hAE : 2*(18+E) ≤ A)
    (G : ℝ) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M T : ℝ) (N m1 m2 : ℕ), 1 ≤ M → 1 ≤ T → 2 ≤ N →
        M ≤ (m1 : ℝ) → (m1 : ℝ) ≤ 2*M → M ≤ (m2 : ℝ) → (m2 : ℝ) ≤ 2*M →
        m1 ≠ m2 → Squarefree m1 → Squarefree m2 → N.Coprime (m1*m2) →
        ∀ (χ : OAI.SevenEighths.HeckeFamily.Character) (g : ℝ → ℂ), (∀ x, ‖g x‖ ≤ G) →
        let P := shiftedABLSourceParameter M T N
        let d := m1.gcd m2
        let D := shiftedCommonPrimePart m1 m2
        let F := N*D^2
        let r := (m1/d)*(m2/d)
        let L := circlePowerScale P A
        let T1 := ⌈1+2*(m1 : ℝ)*T⌉₊
        let T2 := ⌈1+5*(m2 : ℝ)*T/2⌉₊
        circleThetaSourceError χ m1 m2 T1 T2 (shiftedSourceTest g m1)
          (shiftedSourceMajorant m2 T) F r L ≤ C*P^(-E) := by
  obtain ⟨C₀,hC₀,herror⟩ := circleThetaSourceError_bound
  let B := C₀*8^4*G*32^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B+1,by positivity,?_⟩
  intro M T N m1 m2 hM hT hN hm1 hm1' hm2 hm2' hne hs1 hs2 hcop χ g hg
    P d D F r L T1 T2
  have hm1p : 0 < m1 := by exact_mod_cast zero_lt_one.trans_le (hM.trans hm1)
  have hm2p : 0 < m2 := by exact_mod_cast zero_lt_one.trans_le (hM.trans hm2)
  have hNp : 0 < N := by omega
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hF,hr,hFr⟩ := shiftedABLOriginal_cofactors
    hNp hm1p hm2p hne hs1 hs2 hcop
  obtain ⟨hP,hHP,hMP,_,_,_,_,_,hFup,hrup⟩ := shiftedABLOriginal_scale_bounds
    hM hT hN hm1 hm1' hm2 hm2' hne hs1 hs2 hcop
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hL := shiftedABLOriginal_detector_threshold hM hT hN hA hm1 hm1' hm2 hm2'
    hne hs1 hs2 hcop
  obtain ⟨hT1,hT2,hfreq⟩ := shiftedABLOriginal_sourceCutoffs hP1 hHP
    (zero_le_one.trans hM) (zero_le_one.trans hT) hm1' hm2' hMP
  have hsource1 (n : ℕ) (_hn : n ∈ Finset.Icc 1 T1) : ‖shiftedSourceTest g m1 n‖ ≤ G :=
    hg _
  have hsource2 (n : ℕ) (_hn : n ∈ Finset.Icc 1 T2) : ‖shiftedSourceMajorant m2 T n‖ ≤ 1 :=
    shiftedSourcePlateau_norm _
  have he := herror F r L hF hr hFr hL χ m1 m2 T1 T2 hm1p hs1
    (shiftedSourceTest g m1) (shiftedSourceMajorant m2 T) G 1 hG zero_le_one hsource1 hsource2
  have hF5 : (F : ℝ) ≤ P^5 := by
    change (F : ℝ) ≤ P^(5 : ℝ) at hFup
    norm_num at hFup
    exact hFup
  have hr5 : (r : ℝ) ≤ P^5 := by
    change (r : ℝ) ≤ P^(5 : ℝ) at hrup
    norm_num at hrup
    exact hrup
  calc
    _ ≤ C₀*((T1 : ℝ)*T2)^2*G*1*(F : ℝ)*(r : ℝ)*
        ((((m2/d)*T1+(m1/d)*T2 : ℕ) : ℝ))^2/Real.sqrt L := he
    _ ≤ C₀*((8*P)*(8*P))^2*G*1*P^5*P^5*(32*P^2)^2/Real.sqrt L := by gcongr
    _ = B*(P^(18 : ℝ)/Real.sqrt L) := by dsimp [B]; norm_num [Real.rpow_natCast]; ring
    _ ≤ B*P^(-E) := mul_le_mul_of_nonneg_left (circlePowerScale_decay hP hAE) hB
    _ ≤ (B+1)*P^(-E) := by gcongr; linarith

end ArtinMatthews
