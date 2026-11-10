module

public import ArtinMatthews.CubicThetaActualCuspFormBase
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
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

/-! Exact comparison of the proved theta level with the specified Hecke
residue modulus. No minimal-conductor or newform assertion is made. -/
namespace ArtinMatthews

/-- The explicit compatible level is eight times three times the norm of
the specified residue modulus `(9 A)`. -/
theorem cubicNumeratorThetaLevel_eq_modulusNorm (A : ℤ) (hA : A ≠ 0) :
    cubicNumeratorThetaLevel A =
      8 * (3 * (cubicNumeratorHeckeCharacter A hA).modulus.absNorm) := by
  rw [cubicNumeratorThetaLevel_eq, cubicNumeratorHeckeCharacter_modulus_absNorm]
  ring

theorem cubicNumeratorTheta_modulusNorm_three_dvd_level (A : ℤ) (hA : A ≠ 0) :
    3 * (cubicNumeratorHeckeCharacter A hA).modulus.absNorm ∣
      cubicNumeratorThetaLevel A := by
  rw [cubicNumeratorThetaLevel_eq_modulusNorm A hA]
  exact dvd_mul_left _ _

end ArtinMatthews
