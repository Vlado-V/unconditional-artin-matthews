module

public import ArtinMatthews.SourceArchDiagonalDerivative
public import ArtinMatthews.SourceArchUpperDerivative
public import ArtinMatthews.SourceArchCasimirLogIdentities
public import ArtinMatthews.SourceArchDiagonalCompact
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceArchUpperSection_zero (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) :
    sourceArchUpperSection s g z 0 = sourceArchSphericalGL s g := by
  simp only [sourceArchUpperSection, Complex.ofReal_zero, zero_mul,
    sourceKPUpperMatrix_zero, mul_one]

theorem sourceArchDiagonalSection_zero (s : ℂ) (g : GL (Fin 2) ℂ) :
    sourceArchDiagonalSection s g 0 = sourceArchSphericalGL s g := by
  rw [sourceArchDiagonalSection, sourceArchPositiveDiagonal_zero, mul_one]

def sourceArchSphericalRightCasimir (s : ℂ) (g : GL (Fin 2) ℂ) : ℂ :=
  -(deriv (deriv (sourceArchUpperSection s g 1)) 0 +
    deriv (deriv (sourceArchUpperSection s g Complex.I)) 0 +
    deriv (deriv (sourceArchDiagonalSection s g)) 0 -
    2 * deriv (sourceArchDiagonalSection s g) 0)

theorem sourceArchSphericalRightCasimir_eq (s : ℂ) (g : GL (Fin 2) ℂ) :
    sourceArchSphericalRightCasimir s g = (1-4*s^2)*sourceArchSphericalGL s g := by
  have hs : (sourceArchUpperLogOne g 1 0 : ℂ)^2 +
      (sourceArchUpperLogOne g Complex.I 0 : ℂ)^2 +
      (sourceArchDiagonalLogOne g 0 : ℂ)^2 = 1 := by
    exact_mod_cast (sourceArchCasimir_log_identities g).1
  have hl : (sourceArchUpperLogTwo g 1 0 : ℂ) +
      (sourceArchUpperLogTwo g Complex.I 0 : ℂ) +
      (sourceArchDiagonalLogTwo g 0 : ℂ) - 2*(sourceArchDiagonalLogOne g 0 : ℂ) = -2 := by
    exact_mod_cast (sourceArchCasimir_log_identities g).2
  have he : sourceArchSphericalRightCasimir s g =
      -((2*s+1)^2*((sourceArchUpperLogOne g 1 0 : ℂ)^2 +
          (sourceArchUpperLogOne g Complex.I 0 : ℂ)^2 + (sourceArchDiagonalLogOne g 0 : ℂ)^2) +
        (2*s+1)*((sourceArchUpperLogTwo g 1 0 : ℂ) +
          (sourceArchUpperLogTwo g Complex.I 0 : ℂ) + (sourceArchDiagonalLogTwo g 0 : ℂ) -
          2*(sourceArchDiagonalLogOne g 0 : ℂ))) * sourceArchSphericalGL s g := by
    rw [sourceArchSphericalRightCasimir, sourceArchUpperSection_deriv_two,
      sourceArchUpperSection_deriv_two, sourceArchDiagonalSection_deriv_two,
      sourceArchDiagonalSection_deriv]
    simp only [sourceArchUpperSectionTwo, sourceArchDiagonalSectionTwo,
      sourceArchDiagonalSectionOne, sourceArchUpperSection_zero, sourceArchDiagonalSection_zero]
    ring
  rw [he,hs,hl]
  ring

end
end ArtinMatthews.SourceArchJacquet
