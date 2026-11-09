module

public import ArtinMatthews.RoughCharacterCounting
public import ArtinMatthews.MarkedSieveMertens


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rough-character count at the genuine prime cutoff W, with
its literal Euler product and no assumed distribution estimate. -/
noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators Classical

/-- Every prime factor of a positive modulus q≤W is in the actual sieve set. -/
theorem rough_primesLE_covers_modulus {q : ℕ} [NeZero q] (W : ℝ) (hq : (q : ℝ) ≤ W) :
    ∀ p : ℕ, p.Prime → p ∣ q → p ∈ Nat.primesLE ⌊W⌋₊ := by
  have hW : 0 ≤ W := (Nat.cast_nonneg q).trans hq
  have hqW : q ≤ ⌊W⌋₊ := (Nat.le_floor_iff hW).mpr hq
  intro p hp hpq
  exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (NeZero.pos q) hpq).trans hqW, hp⟩

/-- Uniform actual principal/nonprincipal interval count at the prime cutoff. -/
theorem rough_character_primesLE_Ioc_error_numeric {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (W : ℝ) (r M N : ℕ) (hq : (q : ℝ) ≤ W) :
    ‖roughCharacterIocSum χ (Nat.primesLE ⌊W⌋₊) M N -
      (if χ = 1 then ((((N - M : ℕ) : ℝ) * markedSieveEulerProduct W : ℝ) : ℂ) else 0)‖ ≤
      2 * ((N - M : ℕ) : ℝ) *
        ((∑ p ∈ Nat.primesLE ⌊W⌋₊, 1 / (p : ℝ)) ^ (r + 1) / ((r + 1).factorial : ℝ)) +
      W ^ (r + 1) + ((q : ℝ) + 2) * (r + 1 : ℕ) * W ^ r := by
  have hW : 0 ≤ W := (Nat.cast_nonneg q).trans hq
  have hqW : q ≤ ⌊W⌋₊ := (Nat.le_floor_iff hW).mpr hq
  have hv : 1 ≤ ⌊W⌋₊ := (NeZero.pos q).trans_le hqW
  have hh := rough_character_Ioc_error_numeric χ (Nat.primesLE ⌊W⌋₊) r M N ⌊W⌋₊
    (fun _ hp => Nat.prime_of_mem_primesLE hp) (fun _ hp => Nat.le_of_mem_primesLE hp) hv
    (rough_primesLE_covers_modulus W hq)
  change ‖roughCharacterIocSum χ (Nat.primesLE ⌊W⌋₊) M N -
    (if χ = 1 then ((((N - M : ℕ) : ℝ) * markedSieveEulerProduct W : ℝ) : ℂ) else 0)‖ ≤ _ at hh
  apply hh.trans
  have h1 : (⌊W⌋₊ : ℝ) ^ (r + 1) ≤ W ^ (r + 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hW) _
  have h2 : (⌊W⌋₊ : ℝ) ^ r ≤ W ^ r :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hW) _
  exact add_le_add (add_le_add le_rfl h1)
    (mul_le_mul_of_nonneg_left h2 (by positivity))

/-- Prefix form Rχ(X)=δχ V(W)X plus the actual finite Bonferroni error. -/
theorem rough_character_primesLE_prefix_error {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (W : ℝ) (r X : ℕ) (hq : (q : ℝ) ≤ W) :
    ‖(∑ n ∈ Ioc 0 X,
        (if ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬ p ∣ n then (1 : ℂ) else 0) * χ (n : ZMod q)) -
      (if χ = 1 then (((X : ℝ) * markedSieveEulerProduct W : ℝ) : ℂ) else 0)‖ ≤
      2 * (X : ℝ) *
        ((∑ p ∈ Nat.primesLE ⌊W⌋₊, 1 / (p : ℝ)) ^ (r + 1) / ((r + 1).factorial : ℝ)) +
      W ^ (r + 1) + ((q : ℝ) + 2) * (r + 1 : ℕ) * W ^ r := by
  simpa only [roughCharacterIocSum, Nat.sub_zero] using
    rough_character_primesLE_Ioc_error_numeric χ W r 0 X hq

end ArtinMatthews
