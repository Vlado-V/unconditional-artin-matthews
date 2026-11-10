module

public import ArtinMatthews.ShiftedVoronoiCharacter
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The character scalar in paper (5.8), including the negative sign. -/

namespace ArtinMatthews

@[simp] theorem cubicThetaNebentypus_mul (x y : ℤ) :
    cubicThetaNebentypus (x*y) = cubicThetaNebentypus x*cubicThetaNebentypus y := by
  simp [cubicThetaNebentypus, map_mul]

theorem cubicThetaNebentypus_square {a : ℕ} (ha : a.Coprime 3) :
    cubicThetaNebentypus a ^ 2 = 1 := by
  have hunit := (ZMod.isUnit_iff_coprime a 3).mpr ha
  have hs := quadraticChar_sq_one hunit.ne_zero
  change ((quadraticChar (ZMod 3) (a : ZMod 3) : ℤ) : ℂ)^2 = 1
  exact_mod_cast hs

/-- The extra additive numerator factor is one modulo the character
conductor, since q/d is a multiple of three. -/
theorem cubicThetaNebentypus_correction {q d : ℕ} (h3 : 3 ∣ q/d) (j : ℤ) :
    cubicThetaNebentypus (1+j*(q/d : ℕ)) = 1 := by
  have hz : ((q/d : ℕ) : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h3
  unfold cubicThetaNebentypus
  simp only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast,
    hz, mul_zero, add_zero, map_one]

/-- Both Voronoi character factors simplify to the stated scalar, with
no residual dependence on the circle numerator a or congruence class j. -/
theorem doubleVoronoi_character_product {q d a : ℕ}
    (hdq : d ∣ q) (h3 : 3 ∣ q/d) (ha : a.Coprime q)
    (m₃ m₄ j : ℤ) :
    cubicThetaNebentypus (m₄*a*(1+j*(q/d : ℕ))) *
        cubicThetaNebentypus (-m₃*a) = cubicThetaNebentypus (-m₃*m₄) := by
  have h3q : 3 ∣ q := h3.trans (Nat.div_dvd_of_dvd hdq)
  have ha3 : a.Coprime 3 := Nat.Coprime.of_dvd_right h3q ha
  rw [cubicThetaNebentypus_mul, cubicThetaNebentypus_correction h3,
    mul_one, cubicThetaNebentypus_mul, cubicThetaNebentypus_mul]
  calc
    _ = cubicThetaNebentypus (-m₃) * cubicThetaNebentypus m₄ *
        cubicThetaNebentypus a ^ 2 := by ring
    _ = _ := by rw [cubicThetaNebentypus_square ha3, mul_one,
      ← cubicThetaNebentypus_mul]

end ArtinMatthews
