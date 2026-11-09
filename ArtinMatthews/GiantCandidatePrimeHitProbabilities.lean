module

public import ArtinMatthews.GiantCandidatePrimeHitCounts
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! Exact single-prime model probabilities and their reciprocal-prime
upper bounds for fixed ordered tuple length. -/

namespace ArtinMatthews
noncomputable section

def giantCandidatePrimeHitProbability (p j : ℕ) [NeZero p] (side : GiantCandidateHitSide) : ℝ :=
  ((giantCandidatePrimeHitMask p j side).card:ℝ)/(p:ℝ)^j

theorem giantCandidatePrimeHitProbability_predecessor (p j : ℕ) [Fact p.Prime] (hj : 0<j) :
    giantCandidatePrimeHitProbability p j .predecessor = ((p:ℝ)-1)^(j-1)/(p:ℝ)^j := by
  have hp := (Fact.out : p.Prime)
  cases j with
  | zero => omega
  | succ j =>
    change ((giantCandidatePrimeHitMask p (j+1) .predecessor).card:ℝ)/(p:ℝ)^(j+1) =
      ((p:ℝ)-1)^(j+1-1)/(p:ℝ)^(j+1)
    rw [giantCandidatePrimeHitMask_predecessor_card_succ,Nat.cast_pow,Nat.cast_sub hp.one_le,
      Nat.cast_one,Nat.add_sub_cancel]

theorem giantCandidatePrimeHitProbability_predecessor_ratio (p j : ℕ) [Fact p.Prime] (hj : 0<j) :
    giantCandidatePrimeHitProbability p j .predecessor = (1-1/(p:ℝ))^(j-1)/(p:ℝ) := by
  have hpR : (0:ℝ)<p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have he : 1-1/(p:ℝ) = ((p:ℝ)-1)/(p:ℝ) := by rw [sub_div,div_self hpR.ne']
  rw [giantCandidatePrimeHitProbability_predecessor p j hj,he,div_pow,div_div,← pow_succ,
    Nat.sub_add_cancel hj]

theorem giantCandidatePrimeHitProbability_product (p j : ℕ) [Fact p.Prime] :
    giantCandidatePrimeHitProbability p j .product = 1-(1-1/(p:ℝ))^j := by
  have hp := (Fact.out : p.Prime)
  have hpR : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have hpow : (p-1)^j≤p^j := Nat.pow_le_pow_left (Nat.sub_le _ _) j
  unfold giantCandidatePrimeHitProbability
  rw [giantCandidatePrimeHitMask_product_card,Nat.cast_sub hpow,Nat.cast_pow,Nat.cast_pow,
    Nat.cast_sub hp.one_le,Nat.cast_one,sub_div,div_self (pow_ne_zero _ hpR.ne')]
  have he : 1-1/(p:ℝ) = ((p:ℝ)-1)/(p:ℝ) := by rw [sub_div,div_self hpR.ne']
  rw [he,div_pow]

theorem giantCandidatePrimeHitProbability_nonneg (p j : ℕ) [NeZero p] (side : GiantCandidateHitSide) :
    0≤giantCandidatePrimeHitProbability p j side := by
  unfold giantCandidatePrimeHitProbability
  positivity

private theorem giantCandidate_one_sub_pow_le_mul {t : ℝ} (ht : 0≤t) (ht₁ : t≤1) (j : ℕ) :
    1-(1-t)^j ≤ (j:ℝ)*t := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      _ = 1-(1-t)^j+(1-t)^j*t := by rw [pow_succ]; ring
      _ ≤ (j:ℝ)*t+1*t := add_le_add ih
        (mul_le_mul_of_nonneg_right (pow_le_one₀ (sub_nonneg.mpr ht₁) (by linarith only [ht])) ht)
      _ = _ := by rw [Nat.cast_succ]; ring

theorem giantCandidatePrimeHitProbability_le (p j : ℕ) [Fact p.Prime] (hj : 0<j)
    (side : GiantCandidateHitSide) :
    giantCandidatePrimeHitProbability p j side ≤ (j:ℝ)/(p:ℝ) := by
  have hp := (Fact.out : p.Prime)
  have hpR : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have hp₁ : (1:ℝ)≤p := Nat.one_le_cast.mpr hp.one_le
  have ht : 0≤1/(p:ℝ) := div_nonneg zero_le_one hpR.le
  have ht₁ : 1/(p:ℝ)≤1 := (div_le_one hpR).mpr hp₁
  cases side
  · rw [giantCandidatePrimeHitProbability_predecessor_ratio p j hj]
    apply div_le_div_of_nonneg_right _ hpR.le
    exact (pow_le_one₀ (sub_nonneg.mpr ht₁) (by linarith only [ht])).trans
      (Nat.one_le_cast.mpr hj)
  · rw [giantCandidatePrimeHitProbability_product]
    simpa only [mul_one_div] using giantCandidate_one_sub_pow_le_mul ht ht₁ j

end
end ArtinMatthews
