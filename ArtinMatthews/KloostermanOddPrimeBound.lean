module

public import ArtinMatthews.KloostermanOddPowerGauss


set_option backward.privateInPublic true
@[expose] public section

/-! The actual primitive odd prime-power Kloosterman sum has its square-root bound. -/
noncomputable section
open scoped BigOperators
open OAI.Erdos970.ErdosKloosterman OAI.Erdos970.ErdosKloosterman.PrimePower
namespace ArtinMatthews.PrimePowerWeil

attribute [local instance] Classical.decEq

theorem oddPower_sqrt (p m : ℕ) :
    Real.sqrt ((p^(2*m+1):ℕ):ℝ)=((p^m:ℕ):ℝ)*Real.sqrt p := by
  have he : p^(2*m+1)=(p^m)^2*p := by
    rw [← pow_mul,← pow_succ]
    congr 1
    omega
  rw [he,Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]

theorem standardSum_odd_prime_power_left (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hp2 : p ≠ 2)
    (h k : ℤ) (hh : (h:ZMod p)≠0) :
    ‖standardSum (p^(2*m+1)) h k‖≤2*Real.sqrt ((p^(2*m+1):ℕ):ℝ) := by
  have ha : oddPowerReduction p m (h:OddPowerRing p m)≠0 := by
    simpa only [map_intCast] using hh
  have havg := oddPower_averaged_norm p m hm hp2 (h:OddPowerRing p m) (k:OddPowerRing p m) ha
  have hc : ((stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) (h:OddPowerRing p m) k).card:ℝ)≤
      2*((p^(m+1):ℕ):ℝ) := by
    exact_mod_cast oddPower_stationary_card p m (by omega) hp2 h k hh
  have hp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hprod : ‖sum ZMod.stdAddChar (h:OddPowerRing p m) (k:OddPowerRing p m)‖≤
      2*((p^m:ℕ):ℝ)*Real.sqrt p := by
    apply (mul_le_mul_iff_right₀ hp).mp
    calc
      _ ≤ ((stationaryUnits ((p^(m+1):ℕ):OddPowerRing p m) (h:OddPowerRing p m) k).card:ℝ)*Real.sqrt p := havg
      _ ≤ (2*((p^(m+1):ℕ):ℝ))*Real.sqrt p := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
      _ = (p:ℝ)*(2*((p^m:ℕ):ℝ)*Real.sqrt p) := by
        rw [pow_succ p m,Nat.cast_mul]
        ring
  have hN : p^(2*m+1)=p^(m+1)*p^m := by
    rw [← pow_add]
    congr 1
    omega
  rw [standardSum_modulus_congr _ _ hN,oddPower_sqrt]
  simpa only [standardSum,mul_assoc] using hprod

theorem standardSum_odd_prime_power (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hp2 : p ≠ 2)
    (h k : ℤ) (hnot : (h:ZMod p)≠0 ∨ (k:ZMod p)≠0) :
    ‖standardSum (p^(2*m+1)) h k‖≤2*Real.sqrt ((p^(2*m+1):ℕ):ℝ) := by
  rcases hnot with hh | hk
  · exact standardSum_odd_prime_power_left p m hm hp2 h k hh
  · rw [show standardSum (p^(2*m+1)) h k=standardSum (p^(2*m+1)) k h from
      sum_swap ZMod.stdAddChar (h:ZMod (p^(2*m+1))) (k:ZMod (p^(2*m+1)))]
    exact standardSum_odd_prime_power_left p m hm hp2 k h hk

end ArtinMatthews.PrimePowerWeil
