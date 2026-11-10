module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# Choosing the two quadratic signs modulo eight

The four odd classes modulo eight realize every pair of prescribed quadratic
signs for minus one and two.  The supplementary reciprocity laws then apply
uniformly to every prime in the chosen class.
-/

namespace ArtinMatthews

/-- Congruence to an odd class modulo eight excludes the prime two. -/
theorem prime_ne_two_of_odd_mod_eight {p r : ℕ}
    (hr : Odd r) (hpr : p ≡ r [MOD 8]) : p ≠ 2 := by
  intro hp2
  subst p
  have hr2 := Nat.odd_iff.mp hr
  change 2 % 8 = r % 8 at hpr
  omega

/-- The supplementary quadratic characters depend only on the odd class
modulo eight. -/
theorem supplementary_signs_of_mod_eight {p r : ℕ} [Fact p.Prime]
    (hr : Odd r) (hpr : p ≡ r [MOD 8]) :
    legendreSym p (-1) = ZMod.χ₄ r ∧ legendreSym p 2 = ZMod.χ₈ r := by
  have hp2 := prime_ne_two_of_odd_mod_eight hr hpr
  have h4 : p % 4 = r % 4 := by
    change p % 8 = r % 8 at hpr
    omega
  constructor
  · rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_mod_four p,
      ZMod.χ₄_nat_mod_four r, h4]
  · rw [legendreSym.at_two hp2, ZMod.χ₈_nat_mod_eight p,
      ZMod.χ₈_nat_mod_eight r, hpr]

/-- Every prescribed pair of nonzero signs has an odd residue modulo eight.
The same pair then holds for all prime members of that residue class. -/
theorem exists_mod_eight_sign_choice {sMinusOne sTwo : ℤ}
    (hMinusOne : sMinusOne = 1 ∨ sMinusOne = -1)
    (hTwo : sTwo = 1 ∨ sTwo = -1) :
    ∃ r : ℕ, r ∈ ({1, 3, 5, 7} : Finset ℕ) ∧ Odd r ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≡ r [MOD 8] →
        p ≠ 2 ∧ legendreSym p (-1) = sMinusOne ∧ legendreSym p 2 = sTwo := by
  rcases hMinusOne with rfl | rfl <;> rcases hTwo with rfl | rfl
  · refine ⟨1, by decide, by decide, ?_⟩
    intro p hp hpr
    refine ⟨prime_ne_two_of_odd_mod_eight (by decide : Odd 1) hpr, ?_⟩
    simpa using supplementary_signs_of_mod_eight (by decide : Odd 1) hpr
  · refine ⟨5, by decide, by decide, ?_⟩
    intro p hp hpr
    refine ⟨prime_ne_two_of_odd_mod_eight (by decide : Odd 5) hpr, ?_⟩
    simpa using supplementary_signs_of_mod_eight (by decide : Odd 5) hpr
  · refine ⟨7, by decide, by decide, ?_⟩
    intro p hp hpr
    refine ⟨prime_ne_two_of_odd_mod_eight (by decide : Odd 7) hpr, ?_⟩
    simpa using supplementary_signs_of_mod_eight (by decide : Odd 7) hpr
  · refine ⟨3, by decide, by decide, ?_⟩
    intro p hp hpr
    refine ⟨prime_ne_two_of_odd_mod_eight (by decide : Odd 3) hpr, ?_⟩
    simpa using supplementary_signs_of_mod_eight (by decide : Odd 3) hpr

end ArtinMatthews
