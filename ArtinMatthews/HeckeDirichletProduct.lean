module

public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.HeckeDirichletTwist
public import ArtinMatthews.HeckeDirichletTwistNonprincipal
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

/-! Combining two literal Dirichlet factors at the product modulus,
including nonunits. This treats the fixed extra character in Lemma 4.1. -/

noncomputable section
namespace ArtinMatthews
open OAI OAI.SevenEighths

def heckeDirichletProduct {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ϑ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (dvd_mul_right q r) * ϑ.changeLevel (dvd_mul_left r q)

theorem heckeDirichletProduct_natCast {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ϑ : DirichletCharacter ℂ r) (n : ℕ) :
    heckeDirichletProduct χ ϑ n = χ n*ϑ n := by
  by_cases hn : n.Coprime (q*r)
  · have hχ := DirichletCharacter.changeLevel_eq_cast_of_dvd χ
      (dvd_mul_right q r) (ZMod.unitOfCoprime n hn)
    have hϑ := DirichletCharacter.changeLevel_eq_cast_of_dvd ϑ
      (dvd_mul_left r q) (ZMod.unitOfCoprime n hn)
    simp only [ZMod.coe_unitOfCoprime] at hχ hϑ
    rw [ZMod.cast_natCast (dvd_mul_right q r)] at hχ
    rw [ZMod.cast_natCast (dvd_mul_left r q)] at hϑ
    exact congrArg₂ (·*·) hχ hϑ
  · have hnu : ¬ IsUnit (n : ZMod (q*r)) := by rwa [ZMod.isUnit_iff_coprime]
    rw [(heckeDirichletProduct χ ϑ).map_nonunit hnu]
    by_cases hq : n.Coprime q
    · have hr : ¬ n.Coprime r := fun hr => hn (hq.mul_right hr)
      rw [ϑ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]
    · rw [χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]

theorem idealThetaCoeff_heckeDirichletProduct (η : HeckeFamily.Character)
    {q r : ℕ} [NeZero q] [NeZero r] (χ : DirichletCharacter ℂ q)
    (ϑ : DirichletCharacter ℂ r) (n : ℕ) :
    idealThetaCoeff (heckeDirichletTwist η (heckeDirichletProduct χ ϑ)) n =
      idealThetaCoeff η n*χ n*ϑ n := by
  rw [idealThetaCoeff_heckeDirichletTwist, heckeDirichletProduct_natCast, mul_assoc]

theorem cubicNumeratorHeckeDirichletProduct_nonprincipal (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {q r : ℕ} [NeZero q] [NeZero r] (χ : DirichletCharacter ℂ q)
    (ϑ : DirichletCharacter ℂ r) :
    (heckeDirichletTwist (cubicNumeratorHeckeCharacter A hA)
      (heckeDirichletProduct χ ϑ)).residue ≠ 1 :=
  cubicNumeratorHeckeDirichletTwist_nonprincipal A hA hnoncube (heckeDirichletProduct χ ϑ)

end ArtinMatthews
