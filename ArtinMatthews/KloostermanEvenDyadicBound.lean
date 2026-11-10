module

public import OAI.NumberTheory.Jacobsthal.Estimates.PairCollisionCount
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import OAI.NumberTheory.Jacobsthal.Estimates.PrimitiveThreeQuarters


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine even-power square-root bounds and the fixed-constant dyadic odd-power bound. -/
noncomputable section
open OAI.Erdos970.ErdosKloosterman OAI.Erdos970.ErdosKloosterman.PrimePower
namespace ArtinMatthews.PrimePowerWeil

theorem evenPower_sqrt (p m : ℕ) : Real.sqrt ((p^(2*m):ℕ):ℝ)=((p^m:ℕ):ℝ) := by
  have he : p^(2*m)=(p^m)^2 := by rw [← pow_mul]; congr 1; omega
  rw [he,Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg _)]

theorem standardSum_even_prime_power (p m : ℕ) [Fact p.Prime] (hm : 0<m)
    (h k : ℤ) (hnot : (h:ZMod p)≠0 ∨ (k:ZMod p)≠0) :
    ‖standardSum (p^(2*m)) h k‖≤4*Real.sqrt ((p^(2*m):ℕ):ℝ) := by
  have hbound := primitive_half_bound p m m hm le_rfl h k hnot
  have he : p^(m+m)=p^(2*m) := by congr 1; omega
  rw [standardSum_modulus_congr _ _ he] at hbound
  rw [evenPower_sqrt]
  exact hbound

theorem standardSum_dyadic_odd_power (m : ℕ) (hm : 1≤m) (h k : ℤ)
    (hnot : (h:ZMod 2)≠0 ∨ (k:ZMod 2)≠0) :
    ‖standardSum (2^(2*m+1)) h k‖≤8*Real.sqrt ((2^(2*m+1):ℕ):ℝ) := by
  have hb := primitive_half_bound 2 (m+1) m (by omega) (by omega) h k hnot
  have he : (2:ℕ)^((m+1)+m)=2^(2*m+1) := by congr 1; omega
  rw [standardSum_modulus_congr _ _ he] at hb
  have hsqrt : Real.sqrt ((2^(2*m+1):ℕ):ℝ)=((2^m:ℕ):ℝ)*Real.sqrt 2 := by
    have hn : (2:ℕ)^(2*m+1)=(2^m)^2*2 := by rw [← pow_mul,← pow_succ]; congr 1; omega
    rw [hn,Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
    norm_num
  have htwo : 1≤Real.sqrt (2:ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by norm_num : (1:ℝ)≤2)
  calc
    _ ≤ 4*((2^(m+1):ℕ):ℝ) := hb
    _ = 8*((2^m:ℕ):ℝ) := by rw [pow_succ,Nat.cast_mul]; norm_num; ring
    _ ≤ 8*((2^m:ℕ):ℝ)*Real.sqrt 2 := le_mul_of_one_le_right (by positivity) htwo
    _ = _ := by rw [hsqrt]; ring

end ArtinMatthews.PrimePowerWeil
