module

public import ArtinMatthews.ShiftedABLCirclePrefactor
public import ArtinMatthews.ShiftedABLOriginalParameters


set_option backward.privateInPublic true
@[expose] public section

/-! The totient-normalizer loss is absorbed after the fixed circle power
is chosen, using the actual source cofactor growth. -/

noncomputable section
namespace ArtinMatthews

theorem shiftedABLOriginal_normalizer_budget {A ν : ℝ} (hA : 12 ≤ A) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M T : ℝ) (N m1 m2 : ℕ), 1 ≤ M → 1 ≤ T → 2 ≤ N →
        M ≤ (m1 : ℝ) → (m1 : ℝ) ≤ 2*M → M ≤ (m2 : ℝ) → (m2 : ℝ) ≤ 2*M →
        m1 ≠ m2 → Squarefree m1 → Squarefree m2 → N.Coprime (m1*m2) →
        let P := shiftedABLSourceParameter M T N
        let d := m1.gcd m2
        let D := shiftedCommonPrimePart m1 m2
        let m3 := m1/d
        let m4 := m2/d
        let F := N*D^2
        let r := m3*m4
        let L := circlePowerScale P A
        let Q := circlePowerQ P A
        let Λ := circleNormalizer (circleModuli F r L) (circleSmoothWeight L)
        ‖cubicThetaNebentypus (-((m3 : ℕ) : ℤ)*m4)/
          ((Λ : ℂ)*(F : ℂ)*(Q : ℂ))‖ ≤ C*P^ν/Q^3 := by
  obtain ⟨η,hη,hη1,hloss⟩ := circle_epsilon_budget
    (show 0 ≤ A+3 by linarith) (by norm_num : (0 : ℝ) ≤ 5)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 0) hν (by norm_num : (0 : ℝ) < 1)
  obtain ⟨C,hC,hprefactor⟩ := shiftedABL_circle_prefactor_Q_bound η hη hη1
  refine ⟨C,hC,?_⟩
  intro M T N m1 m2 hM hT hN hm1 hm1' hm2 hm2' hne hs1 hs2 hcop
    P d D m3 m4 F r L Q Λ
  have hm1p : 0 < m1 := by exact_mod_cast zero_lt_one.trans_le (hM.trans hm1)
  have hm2p : 0 < m2 := by exact_mod_cast zero_lt_one.trans_le (hM.trans hm2)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hF,hr,hFr⟩ := shiftedABLOriginal_cofactors
    (by omega : 0 < N) hm1p hm2p hne hs1 hs2 hcop
  obtain ⟨hP,_,_,_,_,_,_,_,_,hrup⟩ := shiftedABLOriginal_scale_bounds
    hM hT hN hm1 hm1' hm2 hm2' hne hs1 hs2 hcop
  have hP1 : 1 ≤ P := by linarith
  have hQup : Q ≤ P^(A+3) := circlePowerQ_le hP (by linarith)
  have hQ0 : 0 ≤ Q := by dsimp [Q,circlePowerQ]; positivity
  have hL := shiftedABLOriginal_detector_threshold hM hT hN hA hm1 hm1' hm2 hm2'
    hne hs1 hs2 hcop
  have hsmall : Q^η*(r : ℝ)^η ≤ P^ν := by
    simpa only [one_mul,zero_mul,Real.rpow_zero,mul_one] using
      hloss P Q (r : ℝ) hP1 hQ0 (Nat.cast_nonneg r) hQup hrup
  calc
    _ ≤ C*(Q^η*(r : ℝ)^η)/Q^3 := hprefactor F r L m3 m4 hF hr hFr hL
    _ ≤ C*P^ν/Q^3 := by gcongr

end ArtinMatthews
