module

public import ArtinMatthews.KummerCyclotomicTowerBase
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ArtinMatthews.KummerCyclotomicTower
public import ArtinMatthews.KummerCyclotomicTowerCyclic
public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import ArtinMatthews.KummerTowerDiscriminant
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Size of the explicit discriminant-times-degree-square integer. This file
proves its arithmetic size only; the local norm/conductor property is a
separate theorem and is not presumed. -/
noncomputable section
namespace ArtinMatthews

/-- The explicit integer proposed by the local Hensel norm construction. -/
def discriminantDegreeModulus (F E : Type*) [Field F] [Field E] [NumberField E]
    [Algebra F E] : ℕ :=
  (NumberField.discr E).natAbs * Module.finrank F E ^ 2

theorem discriminantDegreeModulus_pos (F E : Type*) [Field F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] : 0 < discriminantDegreeModulus F E := by
  exact Nat.mul_pos (Int.natAbs_pos.mpr (NumberField.discr_ne_zero E))
    (pow_pos Module.finrank_pos 2)

theorem discr_dvd_discriminantDegreeModulus (F E : Type*) [Field F] [Field E] [NumberField E]
    [Algebra F E] : (NumberField.discr E).natAbs ∣ discriminantDegreeModulus F E :=
  dvd_mul_right _ _

theorem log_discriminantDegreeModulus (F E : Type*) [Field F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] :
    Real.log (discriminantDegreeModulus F E : ℝ) =
      Real.log |(NumberField.discr E : ℝ)| + 2 * Real.log (Module.finrank F E : ℝ) := by
  have hD : (0 : ℝ) < (NumberField.discr E).natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  have hd : (0 : ℝ) < Module.finrank F E := by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank F E)
  rw [discriminantDegreeModulus, Nat.cast_mul, Nat.cast_pow, Real.log_mul hD.ne' (pow_ne_zero 2 hd.ne'),
    Real.log_pow]
  simp only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_ofNat]

private theorem tower_modulus_log_bound (B : Type*) [Field B]
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    [Algebra B (twelfthKummerField q a)] [FiniteDimensional B (twelfthKummerField q a)]
    (haq : a.natAbs ≤ q) (hd : Module.finrank B (twelfthKummerField q a) ≤ 12 * q) :
    Real.log (discriminantDegreeModulus B (twelfthKummerField q a) : ℝ) ≤
      (72 * (q : ℝ)^2 + 2) * Real.log (12 * q) := by
  rw [log_discriminantDegreeModulus]
  have hdpos : (0 : ℝ) < Module.finrank B (twelfthKummerField q a) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank B (twelfthKummerField q a))
  have hlog : Real.log (Module.finrank B (twelfthKummerField q a) : ℝ) ≤ Real.log (12 * q) :=
    Real.log_le_log hdpos (by exact_mod_cast hd)
  have hD := twelfthKummerField_log_discr_le q a haq
  nlinarith

/-- Polynomial logarithmic size for the explicit integer in the cyclotomic-base tower. -/
theorem twelfthKummer_cyclotomic_discriminantDegreeModulus_log_le
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] (haq : a.natAbs ≤ q) :
    Real.log (discriminantDegreeModulus (twelfthCyclotomicField q) (twelfthKummerField q a) : ℝ) ≤
      (72 * (q : ℝ)^2 + 2) * Real.log (12 * q) := by
  apply tower_modulus_log_bound _ q a haq
  exact (Nat.le_of_dvd (NeZero.pos q) (twelfthKummerField_relative_finrank_dvd q a)).trans
    (by omega)

/-- The same size bound for the actual extension over the original Kummer field. -/
theorem twelfthKummer_original_discriminantDegreeModulus_log_le
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] (haq : a.natAbs ≤ q) :
    Real.log (discriminantDegreeModulus (primeKummerField q a) (twelfthKummerField q a) : ℝ) ≤
      (72 * (q : ℝ)^2 + 2) * Real.log (12 * q) :=
  tower_modulus_log_bound _ q a haq (twelfthKummerField_finrank_over_kummer_le q a)

end ArtinMatthews
