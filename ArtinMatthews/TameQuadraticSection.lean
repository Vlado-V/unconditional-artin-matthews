module

public import ArtinMatthews.TameQuadraticGauss


set_option backward.privateInPublic true
@[expose] public section

/-! The odd-residue-characteristic quadratic Gauss section on valuation and
residue-unit coordinates.  Its defect is computed from the finite Gauss square
identity, including negative valuations.  The identification of this explicit
defect with a local reciprocity Hilbert symbol is a separate statement. -/

namespace ArtinMatthews.QuadraticGauss

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

def tameSection (ψ : AddChar F ℂ) (m : ℤ) (u : Fˣ) : ℂ :=
  if Even m then 1 else residueIndex F ψ * residueCharacter F (u : F)

def tameDefect (m n : ℤ) (u v : Fˣ) : ℂ :=
  residueCharacter F (-1) ^ (m * n) *
    residueCharacter F (u : F) ^ n * residueCharacter F (v : F) ^ m

theorem square_one_zpow {z : ℂ} (hz : z ^ 2 = 1) (m : ℤ) :
    z ^ m = if Even m then 1 else z := by
  rcases sq_eq_one_iff.mp hz with h | h
  · simp [h]
  · simpa only [h] using (neg_one_zpow_eq_ite (α := ℂ) (n := m))

theorem tameSection_even (ψ : AddChar F ℂ) {m : ℤ} (hm : Even m) (u : Fˣ) :
    tameSection ψ m u = 1 := ite_eq_left hm

theorem tameSection_odd (ψ : AddChar F ℂ) {m : ℤ} (hm : ¬ Even m) (u : Fˣ) :
    tameSection ψ m u = residueIndex F ψ * residueCharacter F (u : F) := ite_eq_right hm

theorem tameSection_uniformizer (ψ : AddChar F ℂ) :
    tameSection ψ 1 1 = residueIndex F ψ := by
  simp [tameSection]

theorem tameSection_cocycle (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (m n : ℤ) (u v : Fˣ) :
    tameSection ψ m u * tameSection ψ n v =
      tameDefect m n u v * tameSection ψ (m + n) (u * v) := by
  have hu := residueCharacter_sq (F := F) u.ne_zero
  have hv := residueCharacter_sq (F := F) v.ne_zero
  have hs := residueCharacter_sq (F := F) (neg_ne_zero.mpr one_ne_zero)
  have hg := residueIndex_sq hF ψ hψ
  unfold tameDefect
  rw [square_one_zpow hs, square_one_zpow hu, square_one_zpow hv]
  by_cases hm : Even m <;> by_cases hn : Even n <;>
    simp only [tameSection, Int.even_add, Int.even_mul, hm, hn,
      false_iff, iff_false, not_true_eq_false,
      or_true, or_false, ite_true, ite_false,
      Units.val_mul, map_mul, one_mul, mul_one]
  · calc
      _ = residueIndex F ψ * residueCharacter F (v : F) *
          residueCharacter F (u : F) ^ 2 := by rw [hu, mul_one]
      _ = _ := by ring
  · calc
      _ = residueIndex F ψ * residueCharacter F (u : F) *
          residueCharacter F (v : F) ^ 2 := by rw [hv, mul_one]
      _ = _ := by ring
  · calc
      residueIndex F ψ * residueCharacter F (u : F) *
          (residueIndex F ψ * residueCharacter F (v : F)) =
        residueIndex F ψ ^ 2 * residueCharacter F (u : F) *
          residueCharacter F (v : F) := by ring
      _ = _ := by rw [hg]

theorem tameSection_square_mul (ψ : AddChar F ℂ) (m k : ℤ) (u v : Fˣ) :
    tameSection ψ (m + 2 * k) (u * v ^ 2) = tameSection ψ m u := by
  have hv := residueCharacter_sq (F := F) v.ne_zero
  have hp : Even (m + 2 * k) ↔ Even m := by simp [Int.even_add]
  simp only [tameSection, hp, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
    hv, mul_one]

theorem tameSection_fourth (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (m : ℤ) (u : Fˣ) :
    tameSection ψ m u ^ 4 = 1 := by
  by_cases hm : Even m
  · simp [tameSection, hm]
  · rw [tameSection_odd ψ hm, mul_pow, residueIndex_fourth hF ψ hψ]
    have hu := residueCharacter_sq (F := F) u.ne_zero
    rw [show 4 = 2 * 2 by decide, pow_mul, hu, one_pow, one_mul]

theorem tameSection_sq (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (m : ℤ) (u : Fˣ) :
    tameSection ψ m u ^ 2 = residueCharacter F (-1) ^ m := by
  rw [square_one_zpow (residueCharacter_sq (F := F)
    (neg_ne_zero.mpr one_ne_zero))]
  by_cases hm : Even m
  · simp [tameSection, hm]
  · rw [tameSection_odd ψ hm, mul_pow, residueIndex_sq hF ψ hψ,
      residueCharacter_sq u.ne_zero, mul_one, ite_eq_right hm]

theorem tameSection_ne_zero (hF : ringChar F ≠ 2)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (m : ℤ) (u : Fˣ) :
    tameSection ψ m u ≠ 0 := by
  intro he
  have hf := tameSection_fourth hF ψ hψ m u
  rw [he, zero_pow (by decide : 4 ≠ 0)] at hf
  exact zero_ne_one hf

theorem tameDefect_units (u v : Fˣ) : tameDefect (0 : ℤ) 0 u v = 1 := by
  simp [tameDefect]

theorem tameDefect_uniformizer_unit (u : Fˣ) :
    tameDefect (1 : ℤ) 0 1 u = residueCharacter F (u : F) := by
  simp [tameDefect]

theorem tameDefect_self_uniformizer :
    tameDefect (F := F) (1 : ℤ) 1 1 1 = residueCharacter F (-1) := by
  simp [tameDefect]

end

end ArtinMatthews.QuadraticGauss
