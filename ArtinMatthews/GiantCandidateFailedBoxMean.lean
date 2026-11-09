module

public import ArtinMatthews.GiantCandidateCoinMass
public import ArtinMatthews.GiantCandidateResidueFullDyad


set_option backward.privateInPublic true
@[expose] public section

/-! The discarded mass on a full rough product box is the literal
uniform tuple average of the failed coin mass. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

def giantCandidateFullRoughBox {j : ℕ} (x : ℝ) (H : Fin j → ℕ) : Finset (Fin j → ℕ) :=
  Fintype.piFinset (fun i => giantCandidateRoughFullDyad
    (Real.exp ((Real.log x)^(6/25:ℝ))) (H i))

def giantCandidateFailedBoxMean {j : ℕ} (x threshold c q : ℝ) (H : Fin j → ℕ) : ℝ :=
  (∑ t ∈ giantCandidateFullRoughBox x H,
    giantCandidateFailedCoinMass x threshold c q j (∏ i,t i)) /
      ((giantCandidateFullRoughBox x H).card:ℝ)

theorem giantCandidateFailedBoxMean_mul_card {j : ℕ} (x threshold c q : ℝ) (H : Fin j → ℕ) :
    giantCandidateFailedBoxMean x threshold c q H *
      ((giantCandidateFullRoughBox x H).card:ℝ) =
      ∑ t ∈ giantCandidateFullRoughBox x H,giantCandidateFailedCoinMass x threshold c q j (∏ i,t i) := by
  unfold giantCandidateFailedBoxMean
  by_cases h : (giantCandidateFullRoughBox x H).card = 0
  · rw [card_eq_zero.mp h]
    simp
  · exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)

theorem giantCandidateFailedBoxMean_nonneg_eventually {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) (hj : 0 < j) :
    ∀ᶠ x : ℝ in atTop,∀ threshold : ℝ,∀ H : Fin j → ℕ,
      0 ≤ giantCandidateFailedBoxMean x threshold (giantCandidateCoinScale q j) q H := by
  filter_upwards [giantCandidateCoinMass_actual_bounds hq0 hq1 j hj] with x hx
  intro threshold H
  exact div_nonneg (sum_nonneg (fun t _ => (hx threshold (∏ i,t i)).2.1)) (Nat.cast_nonneg _)

end
end ArtinMatthews
