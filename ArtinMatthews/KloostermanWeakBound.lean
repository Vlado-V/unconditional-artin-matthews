module

public import ArtinMatthews.KloostermanFourthMoment
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import OAI.NumberTheory.Jacobsthal.Estimates.ScalarErrorBudget
public import OAI.NumberTheory.Jacobsthal.Sieve.DivisorLogGrowth


set_option backward.privateInPublic true
@[expose] public section

/-!
# The weak composite-modulus Kloosterman bound

This module connects the actual unit Kloosterman sum used in the fourth-moment
identity with the independently proved standard additive-character sum. The
proved divisor subpower estimate absorbs the divisor-square factor uniformly
over all nonzero moduli and all frequencies.
-/

namespace ArtinMatthews

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false in
/-- The finite-duality indexing character is the standard additive character
at the product of the frequency and the argument. -/
theorem zmodAddEquiv_apply_eq_stdAddChar {N : ℕ} [NeZero N] (h x : ZMod N) :
    AddChar.zmodAddEquiv h x = ZMod.stdAddChar (h * x) := by
  obtain ⟨h, rfl⟩ := ZMod.intCast_surjective h
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective x
  change (AddChar.zmod N (h : ZMod N) (x : ZMod N) : ℂ) = _
  rw [show (h : ZMod N) * (x : ZMod N) = ((h * x : ℤ) : ZMod N) by push_cast; rfl]
  rw [AddChar.zmod_intCast, ZMod.stdAddChar_coe, Circle.coe_exp]
  congr 1
  push_cast
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The actual unit sum in the fourth-moment module is exactly the standard
integer-frequency sum in the existing Kloosterman proof. -/
theorem unitKloostermanSum_eq_standardSum (N : ℕ) [NeZero N] (h k : ZMod N) :
    unitKloostermanSum N h k =
      OAI.Erdos970.ErdosKloosterman.standardSum N (h.val : ℤ) (k.val : ℤ) := by
  classical
  unfold unitKloostermanSum doubleCharacterSum
    OAI.Erdos970.ErdosKloosterman.standardSum OAI.Erdos970.ErdosKloosterman.sum
  apply Finset.sum_congr (by ext u; simp)
  intro u _hu
  rw [zmodAddEquiv_apply_eq_stdAddChar, zmodAddEquiv_apply_eq_stdAddChar,
    ← AddChar.map_add_eq_mul]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The square of the number of divisors has a uniform subpower bound.
This reuses the proved prime-factorization argument, rather than postulating
a divisor estimate as an analytic input. -/
theorem kloosterman_divisor_square_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (N.divisors.card : ℝ) ^ 2 ≤ C * (N : ℝ) ^ ε :=
  OAI.Erdos970.ErdosDivisorBounds.divisor_power_subpower 2 hε

/-- The weak Kloosterman estimate, uniformly over every nonzero modulus and
all integer frequencies, with its required gcd factor retained. -/
theorem standardKloosterman_weak_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (h k : ℤ),
      ‖OAI.Erdos970.ErdosKloosterman.standardSum N h k‖ ≤
        C * (N : ℝ) ^ ((3 / 4 : ℝ) + ε) *
          (Nat.gcd N (Int.gcd h k) : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := kloosterman_divisor_square_subpower hε
  refine ⟨C, hC, ?_⟩
  intro N _inst h k
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hdivN := hdiv N NeZero.one_le
  calc
    _ ≤ (N.divisors.card : ℝ) ^ 2 * (N : ℝ) ^ (3 / 4 : ℝ) *
        (Nat.gcd N (Int.gcd h k) : ℝ) ^ (1 / 4 : ℝ) :=
      OAI.Erdos970.ErdosKloosterman.standardSum_bound N h k
    _ ≤ (C * (N : ℝ) ^ ε) * (N : ℝ) ^ (3 / 4 : ℝ) *
        (Nat.gcd N (Int.gcd h k) : ℝ) ^ (1 / 4 : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdivN (by positivity)) (by positivity)
    _ = _ := by rw [Real.rpow_add hN]; ring

/-- Primitive frequency pairs have the pure `N^(3/4+ε)` bound. -/
theorem standardKloosterman_weak_bound_primitive {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (h k : ℤ),
      Nat.gcd N (Int.gcd h k) = 1 →
      ‖OAI.Erdos970.ErdosKloosterman.standardSum N h k‖ ≤
        C * (N : ℝ) ^ ((3 / 4 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ := standardKloosterman_weak_bound hε
  refine ⟨C, hC, ?_⟩
  intro N _inst h k hgcd
  simpa only [hgcd, Nat.cast_one, Real.one_rpow, mul_one] using hbound N h k

/-- The exact root-module unit sum satisfies the same uniform weak estimate. -/
theorem unitKloostermanSum_weak_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (h k : ZMod N),
      ‖unitKloostermanSum N h k‖ ≤
        C * (N : ℝ) ^ ((3 / 4 : ℝ) + ε) *
          (Nat.gcd N (Nat.gcd h.val k.val) : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := standardKloosterman_weak_bound hε
  refine ⟨C, hC, ?_⟩
  intro N _inst h k
  rw [unitKloostermanSum_eq_standardSum]
  simpa only [Int.gcd_def, Int.natAbs_natCast] using hbound N (h.val : ℤ) (k.val : ℤ)

/-- The root-module unit sum has the pure weak bound at primitive frequency pairs. -/
theorem unitKloostermanSum_weak_bound_primitive {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (h k : ZMod N),
      Nat.gcd N (Nat.gcd h.val k.val) = 1 →
      ‖unitKloostermanSum N h k‖ ≤ C * (N : ℝ) ^ ((3 / 4 : ℝ) + ε) := by
  obtain ⟨C, hC, hbound⟩ := unitKloostermanSum_weak_bound hε
  refine ⟨C, hC, ?_⟩
  intro N _inst h k hgcd
  simpa only [hgcd, Nat.cast_one, Real.one_rpow, mul_one] using hbound N h k

end ArtinMatthews
