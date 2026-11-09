module

public import ArtinMatthews.KloostermanOddPrimeBound
public import ArtinMatthews.KloostermanEvenDyadicBound
public import ArtinMatthews.KloostermanPrimeWeilTransfer


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine primitive square-root bounds for every positive prime-power exponent. -/
noncomputable section
open OAI.Erdos970.ErdosKloosterman
namespace ArtinMatthews.PrimePowerWeil

theorem standardSum_primitive_power_ge_two (p a : ℕ) [Fact p.Prime] (ha : 2 ≤ a)
    (h k : ℤ) (hnot : (h:ZMod p) ≠ 0 ∨ (k:ZMod p) ≠ 0) :
    ‖standardSum (p^a) h k‖≤8*Real.sqrt ((p^a:ℕ):ℝ) := by
  let m := a/2
  have he : a=2*m ∨ a=2*m+1 := by dsimp [m]; omega
  rcases he with he | he
  · have hm : 0 < m := by omega
    rw [he]
    exact (standardSum_even_prime_power p m hm h k hnot).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ) ≤ 8) (Real.sqrt_nonneg _))
  · have hm : 1 ≤ m := by omega
    rw [he]
    by_cases hp2 : p=2
    · subst p
      exact standardSum_dyadic_odd_power m hm h k hnot
    · exact (standardSum_odd_prime_power p m hm hp2 h k hnot).trans
        (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ) ≤ 8) (Real.sqrt_nonneg _))

theorem standardSum_primitive_prime_power (p a : ℕ) [Fact p.Prime] (ha : 0 < a)
    (h k : ℤ) (hnot : (h:ZMod p) ≠ 0 ∨ (k:ZMod p) ≠ 0) :
    ‖standardSum (p^a) h k‖≤8*Real.sqrt ((p^a:ℕ):ℝ) := by
  by_cases ha1 : a=1
  · subst a
    have hb := standardSum_prime_weil_bound p h k hnot
    have hc : 2*Real.sqrt (p:ℝ) ≤ 8*Real.sqrt p :=
      mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ) ≤ 8) (Real.sqrt_nonneg _)
    simpa only [pow_one] using hb.trans hc
  · exact standardSum_primitive_power_ge_two p a (by omega) h k hnot

end ArtinMatthews.PrimePowerWeil
