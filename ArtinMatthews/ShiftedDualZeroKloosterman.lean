module

public import ArtinMatthews.ShiftedDualZeroSummable
public import ArtinMatthews.CircleDetector


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine zero-frequency Kloosterman term has a modulus-independent
Ramanujan bound and an absolutely summable coefficient fiber. -/

noncomputable section
open OAI.Erdos970.ErdosKloosterman
namespace ArtinMatthews

def shiftedDualZeroTerm (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (a b : ℕ → ℂ) (k : ℕ × ℕ) : ℂ :=
  if m4 * k.2 = m3 * k.1 then
    a k.1 * b k.2 *
      ((if Int.ModEq (D : ℤ) ((m3 : ℤ)^2 * k.1) ((m4 : ℤ)^2 * k.2) then 1 else 0) *
        sum ZMod.stdAddChar ((m3 : ZMod q) - (m4 : ZMod q))
          (((m3 : ZMod q) * (m4 : ZMod q))⁻¹ *
            ((m4 : ZMod q) * k.2 - (m3 : ZMod q) * k.1)))
  else 0

theorem shiftedDualZeroTerm_norm_le (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (hne : m3 ≠ m4) (a b : ℕ → ℂ) (k : ℕ × ℕ) :
    ‖shiftedDualZeroTerm q D m3 m4 a b k‖ ≤
      (((m3 : ℤ) - m4).natAbs : ℝ)^2 * shiftedDualZeroMajorant m3 m4 a b k := by
  by_cases hz : m4 * k.2 = m3 * k.1
  · have hzq : (m4 : ZMod q) * k.2 = (m3 : ZMod q) * k.1 := by
      simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ZMod q)) hz
    have hd : (m3 : ℤ) - m4 ≠ 0 := by
      intro h
      have he := sub_eq_zero.mp h
      exact hne (by exact_mod_cast he)
    have hram := primitiveCircleSum_norm_le q hd
    rw [primitiveCircleSum_eq, ← ordinaryKloosterman_zero_eq_ramanujanSum] at hram
    simp only [Int.cast_sub, Int.cast_natCast] at hram
    simp only [shiftedDualZeroTerm, shiftedDualZeroMajorant, ite_eq_left hz, hzq, sub_self, mul_zero]
    split_ifs with hc
    · simpa only [one_mul, norm_mul, mul_comm] using
        mul_le_mul_of_nonneg_left hram (norm_nonneg (a k.1 * b k.2))
    · simp only [zero_mul, mul_zero, norm_zero]
      positivity
  · simp only [shiftedDualZeroTerm, shiftedDualZeroMajorant, ite_eq_right hz, norm_zero, mul_zero, le_refl]

theorem shiftedDualZeroTerm_summable_bound (q : ℕ) [NeZero q] (D m3 m4 : ℕ)
    (hm3 : 0 < m3) (hm4 : 0 < m4) (hne : m3 ≠ m4)
    (a b : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖^2))
    (hb : Summable (fun n => ‖b n‖^2)) :
    Summable (shiftedDualZeroTerm q D m3 m4 a b) ∧
      ‖∑' k, shiftedDualZeroTerm q D m3 m4 a b k‖ ≤
        (((m3 : ℤ) - m4).natAbs : ℝ)^2 *
          (((∑' n, ‖a n‖^2) + (∑' n, ‖b n‖^2)) / 2) := by
  obtain ⟨hs, hsum⟩ := shiftedDualZeroMajorant_summable m3 m4 hm3 hm4 a b ha hb
  let R : ℝ := (((m3 : ℤ) - m4).natAbs : ℝ)^2
  have hp := shiftedDualZeroTerm_norm_le q D m3 m4 hne a b
  have hnorm : Summable (fun k => ‖shiftedDualZeroTerm q D m3 m4 a b k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp (hs.mul_left R)
  refine ⟨hnorm.of_norm, ?_⟩
  calc
    _ ≤ ∑' k, ‖shiftedDualZeroTerm q D m3 m4 a b k‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k, R * shiftedDualZeroMajorant m3 m4 a b k :=
      hnorm.tsum_le_tsum hp (hs.mul_left R)
    _ = R * ∑' k, shiftedDualZeroMajorant m3 m4 a b k := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)

end ArtinMatthews
