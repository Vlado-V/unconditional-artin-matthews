module

public import ArtinMatthews.SourceArchProjectiveUpperAction
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

/-! Equivariance of every actual matrix Gram coordinate under the projective action. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

def sourceArchUpperOrigin : SourceArchUpperHalfSpace := (0, ⟨1, zero_lt_one⟩)

lemma sourceArchUpperHalfSection_origin : sourceArchUpperHalfSection sourceArchUpperOrigin = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceArchUpperHalfSection, sourceArchUpperOrigin, upperSection] <;> rfl

lemma sourceArchGLUpperAction_origin (a : GL (Fin 2) ℂ) :
    sourceArchGLUpperAction a sourceArchUpperOrigin = sourceArchGramCoordinates a := by
  rw [sourceArchGLUpperAction, sourceArchUpperHalfSection_origin, mul_one]

lemma sourceArchGramCoordinates_mul (a b : GL (Fin 2) ℂ) :
    sourceArchGramCoordinates (a * b) =
      sourceArchGLUpperAction a (sourceArchGramCoordinates b) := by
  rw [← sourceArchGLUpperAction_origin, sourceArchGLUpperAction_mul,
    sourceArchGLUpperAction_origin]

end
end ArtinMatthews.SourceArchJacquet
