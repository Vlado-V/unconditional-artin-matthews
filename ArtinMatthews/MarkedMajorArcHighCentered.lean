module

public import ArtinMatthews.MarkedMajorArcCenteredCoefficient
public import ArtinMatthews.MarkedFrequencyShiftBudget


set_option backward.privateInPublic true
@[expose] public section

/-! High-frequency branch of the literal modulated long coefficient, with
all polynomial modulation and original exponential-times-polynomial upper
frequency ranges retained. -/
namespace ArtinMatthews
open Filter
open scoped Topology

 theorem marked_major_high_centered_cancellation (a η τ C b K P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hP : 0 ≤ P) :
    ∃ T : ℝ, 0 < T ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (modulation t H u v : ℝ),
        (q:ℝ) ≤ L^a → |modulation| ≤ L^C →
        L^T ≤ |t| → |t| ≤ K*Real.exp L*L^b →
        Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*L) →
        ‖markedMajorCenteredSum χ (Real.exp (L^(6/25:ℝ))) modulation t H u v‖ ≤ L^(-P) := by
  obtain ⟨T₁,hT₁,hprime⟩ := marked_major_high_prime_normalized a η τ (P+1)
    ha hη hτ (by linarith)
  obtain ⟨T₂,hT₂,hrough⟩ := marked_major_high_rough_cancellation a τ (P+1) ha hτ (by linarith)
  obtain ⟨T,hT,hshift⟩ := marked_frequency_shift_window (max T₁ T₂) C b K
    (hT₁.trans_le (le_max_left _ _))
  refine ⟨T,hT,?_⟩
  filter_upwards [hprime,hrough,hshift,eventually_ge_atTop (6:ℝ)] with L hp hr hs hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  intro q _ χ modulation t H u v hq hmod ht hthi hH hHu huv hvH hvhi
  have hwindow := hs t modulation ht hthi hmod
  have hlow₁ : L^T₁ ≤ |t+modulation| :=
    (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)).trans hwindow.1
  have hlow₂ : L^T₂ ≤ |t+modulation| :=
    (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)).trans hwindow.1
  have hprime' := hp q hq χ (t+modulation) H u v hlow₁ hwindow.2 hH hHu huv hvH hvhi
  have hrough' := hr q χ (t+modulation) H u v hq hlow₂ hwindow.2 hH hHu huv hvH
  have hu : 0 ≤ u := ((Real.exp_pos _).trans_le (hH.trans hHu)).le
  rw [marked_centered_sum_eq χ _ modulation t H u v hu]
  calc
    _ ≤ ‖markedMajorNormalizedPrimeSum χ (t+modulation) H u v‖+
        ‖markedRoughCharacterSum χ (Real.exp (L^(6/25:ℝ))) (t+modulation) H u v‖ := norm_sub_le _ _
    _ ≤ 5*L^(-(P+1))+L^(-(P+1)) := add_le_add hprime' hrough'
    _ = L^(-P)*(6/L) := by
      rw [show -(P+1) = -P+(-1) by ring,Real.rpow_add hLp,Real.rpow_neg_one]
      ring
    _ ≤ L^(-P)*1 := mul_le_mul_of_nonneg_left ((div_le_one hLp).mpr hL)
      (Real.rpow_nonneg hLp.le _)
    _ = _ := mul_one _

end ArtinMatthews
