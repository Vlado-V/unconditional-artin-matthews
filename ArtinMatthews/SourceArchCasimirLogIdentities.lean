module

public import ArtinMatthews.SourceArchDiagonalLog
public import ArtinMatthews.SourceArchUpperLogDerivative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

theorem sourceArchCasimir_log_identities (g : GL (Fin 2) ℂ) :
    (sourceArchUpperLogOne g 1 0)^2 + (sourceArchUpperLogOne g Complex.I 0)^2 +
        (sourceArchDiagonalLogOne g 0)^2 = 1 ∧
    sourceArchUpperLogTwo g 1 0 + sourceArchUpperLogTwo g Complex.I 0 +
        sourceArchDiagonalLogTwo g 0 - 2*sourceArchDiagonalLogOne g 0 = -2 := by
  let c := g 1 0
  let d := g 1 1
  let a := ‖c‖^2
  let b := ‖d‖^2
  let q := a+b
  let u := (star d*c).re
  let v := (star d*c).im
  have hq : q ≠ 0 := (sourceArchBottomNorm_pos g).ne'
  have hn : u^2+v^2=a*b := by
    calc
      _ = Complex.normSq (star d*c) := by simp [u, v, Complex.normSq_apply, pow_two]
      _ = ‖star d*c‖^2 := Complex.normSq_eq_norm_sq _
      _ = a*b := by simp only [norm_mul, norm_star, mul_pow]; dsimp [a,b]; ring
  have hqu (z : ℂ) : sourceArchUpperDenominator g z 0=q := by
    simp [sourceArchUpperDenominator, q, a, b, c, d]
  have hwa : sourceArchDiagonalWeight g 0=a := by simp [sourceArchDiagonalWeight, a, c]
  have hqa : sourceArchDiagonalDenominator g 0=q := by
    simp [sourceArchDiagonalDenominator, hwa, q, b, d]
  have hu : sourceArchUpperLogOne g 1 0= -2*u/q := by
    rw [sourceArchUpperLogOne, hqu, sourceArchUpperDenominatorOne]
    simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_one]
    dsimp [u,c,d]
    ring
  have hi : (star d*(c*Complex.I)).re= -v := by
    rw [← mul_assoc]
    simp [v]
  have hv : sourceArchUpperLogOne g Complex.I 0=2*v/q := by
    rw [sourceArchUpperLogOne, hqu, sourceArchUpperDenominatorOne]
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    change -(2*(star d*(c*Complex.I)).re/q)=2*v/q
    rw [hi]
    ring
  have ha : sourceArchDiagonalLogOne g 0=1-2*a/q := by
    rw [sourceArchDiagonalLogOne, hwa, hqa]
  have ha2 : sourceArchDiagonalLogTwo g 0=4*(a/q)^2-4*a/q := by
    rw [sourceArchDiagonalLogTwo, hwa, hqa]
  have hu2 (z : ℂ) : sourceArchUpperLogTwo g z 0 =
      (sourceArchUpperLogOne g z 0)^2 - 2*‖c*z‖^2/q := by
    rw [sourceArchUpperLogTwo, sourceArchUpperLogOne, hqu, sourceArchUpperDenominatorTwo]
    dsimp [c]
    ring
  have hs : (-2*u/q)^2+(2*v/q)^2+(1-2*a/q)^2=1 := by
    field_simp [hq]
    dsimp [q]
    nlinarith only [hn]
  have hl : ((-2*u/q)^2-2*a/q)+((2*v/q)^2-2*a/q)+
      (4*(a/q)^2-4*a/q)-2*(1-2*a/q)= -2 := by
    field_simp [hq]
    dsimp [q]
    nlinarith only [hn]
  constructor
  · rw [hu,hv,ha]
    exact hs
  · rw [hu2,hu2,hu,hv,ha,ha2]
    simpa only [mul_one, norm_mul, Complex.norm_I] using hl

end
end ArtinMatthews.SourceArchJacquet
