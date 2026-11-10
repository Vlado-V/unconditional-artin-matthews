module

public import ArtinMatthews.QuadraticProgression
public import ArtinMatthews.SquareClassDichotomy
public import ArtinMatthews.ObstructionB
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The split and nonsplit modulo-three branches of the quadratic progression. -/

namespace ArtinMatthews

theorem squareClassCharacter_neg_three (f : RationalSquareClass →ₗ[ZMod 2] ZMod 2) :
    squareClassCharacter f (-3) = paritySign (f negativeThreeSquareClass) := by
  rw [squareClassCharacter_apply f (-3) (by norm_num)]
  have hclass : nonzeroIntegerSquareClass (-3) (by norm_num) = negativeThreeSquareClass := by
    unfold nonzeroIntegerSquareClass negativeThreeSquareClass negativeThreeUnit
    congr 1
  rw [hclass]

theorem two_mod_three_of_legendre_three_eq_neg_one {p : ℕ}
    (h : legendreSym 3 p = -1) : p % 3 = 2 := by
  have hmod := legendreSym.mod 3 (p : ℤ)
  rw [h] at hmod
  have hc : ((p : ℤ) % (3 : ℕ)) = (p % 3 : ℕ) := by omega
  rw [hc] at hmod
  have hr := Nat.mod_lt p (by decide : 0 < 3)
  interval_cases hh : p % 3
  · norm_num [legendreSym, quadraticChar] at hmod
  · norm_num at hmod
  · rfl

/-- The explicit properties of the progression used before the analytic sieve. -/
def IsQuadraticProgressionFor (S : Finset ℤ) (u r3 : ℕ) : Prop :=
  u < quadraticModulus S ∧ Nat.Coprime u (quadraticModulus S) ∧
    ∀ (p : ℕ) [Fact p.Prime], p ≡ u [MOD quadraticModulus S] →
      p ≠ 2 ∧ p % 3 = r3 ∧ (∀ a ∈ S, legendreSym p a = -1) ∧
      ∀ q ∈ quadraticPrimeSupport S, 3 < q → p % q ≠ 1

/-- A functional prescribing the quadratic signs determines the modulo-three
branch as well. -/
theorem exists_quadratic_progression_with_mod_three {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0) (f : RationalSquareClass →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ a : {a // a ∈ S}, f (baseSquareClass hzero a) = 1) :
    ∃ u, IsQuadraticProgressionFor S u
      (if f negativeThreeSquareClass = 0 then 1 else 2) := by
  classical
  obtain ⟨u, hu, hcop, hprog⟩ := exists_quadratic_progression_for_functional hzero f
  refine ⟨u, hu, hcop, ?_⟩
  intro p hp hpu
  obtain ⟨hp2, hbase, hneg3, havoid⟩ := hprog p hpu
  refine ⟨hp2, ?_, ?_, havoid⟩
  · have h3 : legendreSym 3 p = paritySign (f negativeThreeSquareClass) := by
      rw [← legendre_neg_three_eq_at_three hp2, hneg3, squareClassCharacter_neg_three]
    by_cases hfd : f negativeThreeSquareClass = 0
    · have h31 : legendreSym 3 p = 1 := by simpa only [hfd, paritySign_zero] using h3
      simpa only [hfd, ↓reduceIte] using one_mod_three_of_legendre_three_eq_one h31
    · have hfd1 := zmod_two_eq_one_of_ne_zero hfd
      have h32 : legendreSym 3 p = -1 := by simpa only [hfd1, paritySign_one] using h3
      simpa only [hfd, ↓reduceIte] using two_mod_three_of_legendre_three_eq_neg_one h32
  · intro a ha
    rw [hbase a ha]
    exact squareClassCharacter_eq_neg_one_on_bases hzero f hf a ha

/-- An even minus-three relation forces every compatible functional to take
value zero at the distinguished square class. -/
theorem functional_neg_three_eq_zero_of_even_relation {S T : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0) (f : RationalSquareClass →ₗ[ZMod 2] ZMod 2)
    (hf : ∀ a : {a // a ∈ S}, f (baseSquareClass hzero a) = 1)
    (hTS : T ⊆ S) (heven : Even T.card)
    (hrel : NegativeThreeRationalSquare (∏ a ∈ T, a)) :
    f negativeThreeSquareClass = 0 := by
  let a : {a // a ∈ T} → ℤ := fun x => x.val
  let ha : ∀ i, a i ≠ 0 := fun i => hzero i.val (hTS i.property)
  have hsum : (∑ i ∈ T.attach, rationalUnitSquareClass (integerUnit a ha i)) =
      negativeThreeSquareClass := by
    apply (sum_integerSquareClass_eq_negativeThree_iff T.attach a ha).mpr
    change NegativeThreeRationalSquare (∏ i ∈ T.attach, (i : ℤ))
    have hprod : (∏ i ∈ T.attach, (i : ℤ)) = ∏ i ∈ T, i :=
      Finset.prod_attach T (fun z : ℤ => z)
    rw [hprod]
    exact hrel
  calc
    f negativeThreeSquareClass = ∑ i ∈ T.attach,
        f (rationalUnitSquareClass (integerUnit a ha i)) := by rw [← hsum, map_sum]
    _ = ∑ _i ∈ T.attach, (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hf ⟨i.val, hTS i.property⟩
    _ = (T.card : ZMod 2) := by simp
    _ = 0 := heven.natCast_zmod_two

/-- The exact split/nonsplit choice of Section 10.1.  The split branch carries
the even minus-three relation explaining why it is necessary. -/
theorem exists_quadratic_progression_dichotomy {S : Finset ℤ}
    (hzero : ∀ a ∈ S, a ≠ 0) (hA : ¬ ObstructionA S) :
    (∃ u, IsQuadraticProgressionFor S u 2) ∨
      ((∃ T : Finset ℤ, T ⊆ S ∧ Even T.card ∧
        NegativeThreeRationalSquare (∏ a ∈ T, a)) ∧
       ∃ u, IsQuadraticProgressionFor S u 1) := by
  rcases minus_three_squareClass_dichotomy hzero hA with ⟨f, hf, hfd⟩ | hrel
  · left
    obtain ⟨u, hu⟩ := exists_quadratic_progression_with_mod_three hzero f hf
    refine ⟨u, ?_⟩
    have hne : f negativeThreeSquareClass ≠ 0 := by rw [hfd]; decide
    simpa only [hne, ↓reduceIte] using hu
  · right
    refine ⟨hrel, ?_⟩
    obtain ⟨T, hTS, heven, hT⟩ := hrel
    obtain ⟨f, hf⟩ := (not_obstructionA_iff_exists_squareClassFunctional hzero).mp hA
    have hfd := functional_neg_three_eq_zero_of_even_relation hzero f hf hTS heven hT
    obtain ⟨u, hu⟩ := exists_quadratic_progression_with_mod_three hzero f hf
    exact ⟨u, by simpa only [hfd, ↓reduceIte] using hu⟩

end ArtinMatthews
