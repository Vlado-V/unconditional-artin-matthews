module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicTheta
public import ArtinMatthews.CubicThetaActualCusps
public import ArtinMatthews.CubicThetaCuspInterface
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

/-! Native cusp vanishing for the actual cubic ideal theta. Holomorphy and
vanishing at cusps are proved; scalar congruence invariance remains separate. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups Topology
open Complex UpperHalfPlane Filter

/-- Actual cubic Hecke theta vanishes at every rational cusp in Mathlib's
native weight-one predicate. -/
theorem cubicNumeratorHeckeTheta_isZeroAt (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsZeroAt c (heckeTheta (cubicNumeratorHeckeCharacter A hA)) 1 :=
  isZeroAt_of_weight_one_cusp_limits _
    (tendsto_cubicNumeratorHeckeTheta_cusp A hA hnoncube) hc

/-- This supplies the native cusp-vanishing condition for any arithmetic
subgroup, independently of the remaining modular transformation law. -/
theorem cubicNumeratorHeckeTheta_isZeroAt_arithmetic (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y ^ 3 = (A : OAI.CubicFirstMoment.Eisenstein))
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsZeroAt c (heckeTheta (cubicNumeratorHeckeCharacter A hA)) 1 :=
  isZeroAt_arithmetic_of_weight_one_cusp_limits _
    (tendsto_cubicNumeratorHeckeTheta_cusp A hA hnoncube) Γ hc

/-- The actual nonconstant cubic Galois character supplies nonprincipality;
the native cusp-vanishing conclusion has no assumed cusp condition. -/
theorem cubicFourier_heckeTheta_isZeroAt {S : Finset ℤ}
    (χ : AddChar (Additive (integerCubicGaloisGroup S)) ℂ) (hχ : χ ≠ 0)
    {A : ℤ} (hA : A ≠ 0) {R : integerCubicField S} (hR0 : R ≠ 0)
    (hR : R ^ 3 = (A : integerCubicField S))
    (hrep : ∀ σ : integerCubicGaloisGroup S,
      χ (Additive.ofMul σ) = ((σ.val R / R : integerCubicField S) : ℂ))
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    OnePoint.IsZeroAt c (heckeTheta (cubicNumeratorHeckeCharacter A hA)) 1 :=
  isZeroAt_of_weight_one_cusp_limits _
    (cubicFourier_heckeTheta_cusp χ hχ hA hR0 hR hrep) hc

end ArtinMatthews
