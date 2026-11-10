module

public import OAI.NumberTheory.DirichletL.Hecke.Family
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The explicit finite modulus used by the cubic numerator character. -/

noncomputable section

namespace ArtinMatthews

open OAI.SevenEighths

local notation "EO" => HeckeFamily.O

/-- The literal modulus of the transported cubic numerator character. -/
def cubicNumeratorHeckeModulus (A : ℤ) : Ideal EO := Ideal.span {9 * (A : EO)}

theorem cubicNumeratorHeckeModulus_ne_bot {A : ℤ} (hA : A ≠ 0) :
    cubicNumeratorHeckeModulus A ≠ ⊥ := by
  apply Ideal.span_singleton_eq_bot.not.mpr
  exact mul_ne_zero (by norm_num) (by exact_mod_cast hA)

/-- The residue modulus has norm `81 |A|²`; no unknown conductor constant
is introduced by changing the Eisenstein-ring model. -/
theorem cubicNumeratorHeckeModulus_absNorm (A : ℤ) :
    (cubicNumeratorHeckeModulus A).absNorm = 81 * A.natAbs ^ 2 := by
  have hrank : Module.finrank ℤ EO = 2 := by
    rw [NumberField.RingOfIntegers.rank HeckeFamily.K,
      IsCyclotomicExtension.Rat.finrank 3 HeckeFamily.K]
    decide
  rw [cubicNumeratorHeckeModulus, Ideal.absNorm_span_singleton]
  rw [show (9 : EO) * (A : EO) = algebraMap ℤ EO (9 * A) by simp]
  rw [Algebra.norm_algebraMap, hrank]
  simp [Int.natAbs_mul, mul_pow]

end ArtinMatthews
