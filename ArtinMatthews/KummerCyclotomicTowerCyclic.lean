module

public import ArtinMatthews.KummerCyclotomicTowerBase
public import ArtinMatthews.KummerRadicalCyclic
public import ArtinMatthews.KummerRadicalGeneration
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual auxiliary radical extension is cyclic, of degree dividing q. -/

set_option maxHeartbeats 800000

noncomputable section
namespace ArtinMatthews

def twelfthBaseRoot (q : ℕ) [NeZero q] : twelfthCyclotomicField q :=
  ⟨primeCyclotomicRoot q,
    primeCyclotomicField_le_twelfthCyclotomicField q (primeCyclotomicRoot_mem q)⟩

theorem twelfthBaseRoot_isPrimitiveRoot (q : ℕ) [NeZero q] :
    IsPrimitiveRoot (twelfthBaseRoot q) q := by
  apply IsPrimitiveRoot.of_map_of_injective (f := (twelfthCyclotomicField q).val)
    (primeCyclotomicRoot_isPrimitiveRoot (NeZero.pos q))
  exact Subtype.val_injective

def twelfthRadicalRoot (q : ℕ) (a : ℤ) : twelfthKummerField q a :=
  IntermediateField.AdjoinSimple.gen (twelfthCyclotomicField q) (primeRadicalRoot q a)

theorem twelfthRadicalRoot_pow (q : ℕ) (a : ℤ) [NeZero q] :
    twelfthRadicalRoot q a ^ q = algebraMap (twelfthCyclotomicField q)
      (twelfthKummerField q a) (a : twelfthCyclotomicField q) := by
  apply Subtype.ext
  exact primeRadicalRoot_pow (NeZero.pos q) a

theorem twelfthRadicalRoot_ne_zero (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    twelfthRadicalRoot q a ≠ 0 := by
  intro h
  exact primeRadicalRoot_ne_zero (NeZero.pos q) (NeZero.ne a)
    (congrArg (fun z : twelfthKummerField q a => (z : ℂ)) h)

/-- The chosen radical genuinely generates K̃ over the actual cyclotomic field. -/
theorem twelfthRadicalRoot_adjoin_eq_top (q : ℕ) (a : ℤ) :
    IntermediateField.adjoin (twelfthCyclotomicField q) {twelfthRadicalRoot q a} = ⊤ := by
  apply adjoinSimple_gen_adjoin_eq_top
  by_cases hq : q = 0
  · subst q
    simp only [primeRadicalRoot, not_lt_zero, dite_false]
    exact isIntegral_zero
  · apply IsIntegral.of_pow (Nat.pos_of_ne_zero hq)
    rw [primeRadicalRoot_pow (Nat.pos_of_ne_zero hq)]
    exact isIntegral_intCast a

instance twelfthKummerField_isCyclic (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    IsCyclic Gal(twelfthKummerField q a/twelfthCyclotomicField q) :=
  radicalExtension_isCyclic (twelfthBaseRoot_isPrimitiveRoot q) (twelfthRadicalRoot_pow q a)
    (twelfthRadicalRoot_ne_zero q a) (twelfthRadicalRoot_adjoin_eq_top q a)

instance twelfthKummerField_isAbelianGalois_over_cyclotomic
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    IsAbelianGalois (twelfthCyclotomicField q) (twelfthKummerField q a) :=
  IsAbelianGalois.of_isCyclic _ _

/-- The actual relative degree divides q, without an irreducibility hypothesis. -/
theorem twelfthKummerField_relative_finrank_dvd (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    Module.finrank (twelfthCyclotomicField q) (twelfthKummerField q a) ∣ q := by
  let : FiniteDimensional (twelfthCyclotomicField q) (twelfthKummerField q a) :=
    Module.Finite.right ℚ (twelfthCyclotomicField q) (twelfthKummerField q a)
  exact radicalExtension_finrank_dvd (twelfthBaseRoot_isPrimitiveRoot q)
    (twelfthRadicalRoot_pow q a) (twelfthRadicalRoot_ne_zero q a)
    (twelfthRadicalRoot_adjoin_eq_top q a)

end ArtinMatthews
