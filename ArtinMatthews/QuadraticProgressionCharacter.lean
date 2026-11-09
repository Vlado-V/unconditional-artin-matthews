module

public import ArtinMatthews.SquareClassDichotomy
public import ArtinMatthews.QuadraticProgressionFactorization


set_option backward.privateInPublic true
@[expose] public section

/-! The sign character induced by a linear functional on rational square classes. -/

namespace ArtinMatthews

def paritySign (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

@[simp] theorem paritySign_zero : paritySign 0 = 1 := rfl
@[simp] theorem paritySign_one : paritySign 1 = -1 := rfl

theorem paritySign_add (x y : ZMod 2) : paritySign (x + y) = paritySign x * paritySign y := by
  fin_cases x <;> fin_cases y <;> rfl

theorem paritySign_cases (x : ZMod 2) : paritySign x = 1 ∨ paritySign x = -1 := by
  by_cases hx : x = 0
  · simp [paritySign, hx]
  · simp [paritySign, hx]

@[simp] theorem rationalUnitSquareClass_one : rationalUnitSquareClass 1 = 0 := by
  change (QuotientAddGroup.mk' _) 0 = 0
  exact map_zero _

theorem rationalUnitSquareClass_mul (u v : ℚˣ) :
    rationalUnitSquareClass (u * v) = rationalUnitSquareClass u + rationalUnitSquareClass v := by
  change (QuotientAddGroup.mk' _) (Additive.ofMul (u * v)) = _
  rw [ofMul_mul, map_add]
  rfl

def nonzeroIntegerSquareClass (a : ℤ) (ha : a ≠ 0) : RationalSquareClass :=
  rationalUnitSquareClass (Units.mk0 (a : ℚ) (by exact_mod_cast ha))

theorem nonzeroIntegerSquareClass_mul (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    nonzeroIntegerSquareClass (a * b) (mul_ne_zero ha hb) =
      nonzeroIntegerSquareClass a ha + nonzeroIntegerSquareClass b hb := by
  unfold nonzeroIntegerSquareClass
  have hu : Units.mk0 ((a * b : ℤ) : ℚ) (by exact_mod_cast mul_ne_zero ha hb) =
      Units.mk0 (a : ℚ) (by exact_mod_cast ha) * Units.mk0 (b : ℚ) (by exact_mod_cast hb) := by
    apply Units.ext
    simp
  rw [hu, rationalUnitSquareClass_mul]

/-- The multiplicative sign on integers prescribed by a square-class functional. -/
noncomputable def squareClassCharacter (f : RationalSquareClass →ₗ[ZMod 2] ZMod 2) : ℤ →*₀ ℤ where
  toFun a := if ha : a = 0 then 0 else paritySign (f (nonzeroIntegerSquareClass a ha))
  map_zero' := dite_eq_left rfl
  map_one' := by simp [nonzeroIntegerSquareClass]
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    simp [ha, hb, mul_ne_zero ha hb, nonzeroIntegerSquareClass_mul, paritySign_add]

theorem squareClassCharacter_apply (f : RationalSquareClass →ₗ[ZMod 2] ZMod 2)
    (a : ℤ) (ha : a ≠ 0) :
    squareClassCharacter f a = paritySign (f (nonzeroIntegerSquareClass a ha)) := by
  simp [squareClassCharacter, ha]

theorem squareClassCharacter_cases (f : RationalSquareClass →ₗ[ZMod 2] ZMod 2)
    (a : ℤ) (ha : a ≠ 0) :
    squareClassCharacter f a = 1 ∨ squareClassCharacter f a = -1 := by
  rw [squareClassCharacter_apply f a ha]
  exact paritySign_cases _

theorem nonzeroIntegerSquareClass_eq_baseSquareClass {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0) (a : {a // a ∈ S}) :
    nonzeroIntegerSquareClass a.val (hzero a.val a.property) = baseSquareClass hzero a := rfl

theorem squareClassCharacter_eq_neg_one_on_bases {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0) (f : RationalSquareClass →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ a : {a // a ∈ S}, f (baseSquareClass hzero a) = 1) :
    ∀ a ∈ S, squareClassCharacter f a = -1 := by
  intro a ha
  rw [squareClassCharacter_apply f a (hzero a ha)]
  change paritySign (f (baseSquareClass hzero ⟨a, ha⟩)) = -1
  rw [hf, paritySign_one]

end ArtinMatthews
