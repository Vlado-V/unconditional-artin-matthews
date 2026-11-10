module

public import ArtinMatthews.MarkedMajorCharacterSource
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

/-! Literal identification of each six-character term with the two actual
endpoint coefficients and the original determinant cutoff. -/
namespace ArtinMatthews
open Finset
noncomputable section

theorem markedMajorIntegerDeterminant_real (z z' : ℕ×(ℕ×ℕ)) :
    (markedMajorIntegerDeterminant z z':ℝ) =
      markedMajorLabelTripleValue z-markedMajorLabelTripleValue z' := by
  simp only [markedMajorIntegerDeterminant,markedMajorLabelTripleValue,
    Int.cast_sub,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]

theorem markedMajor_character_term_eq {J J' : Type*} [Fintype J] [Fintype J']
    (S T : Finset (ℕ×(ℕ×ℕ))) (bands : J → Finset ℕ) (bands' : J' → Finset ℕ)
    (cutoff : ℝ → ℂ) (Y W modulation modulation' : ℝ) (β β' : ℕ → ℂ)
    (ψ : ℝ → ℂ) (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ) :
    markedMajorArcCharacterTerm S T
      (markedMajorBareTripleCoefficient bands cutoff Y W modulation β)
      (markedMajorBareConjugateTripleCoefficient bands' cutoff Y W modulation' β') ψ q χ θ Y =
    ∑ z ∈ S,∑ z' ∈ T,
      (markedMajorLabelTripleCoefficient bands cutoff (markedCoordinateDirichlet q χ 1) θ Y
        (markedCoordinateDirichlet q χ 2) W modulation (fun n => β n*markedCoordinateDirichlet q χ 3 n) z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff (markedCoordinateDirichlet q χ 0) (-θ) Y
        (markedCoordinateDirichlet q χ 4) W modulation' (fun n => β' n*markedCoordinateDirichlet q χ 5 n) z')*
      (ψ ((markedMajorLabelTripleValue z-markedMajorLabelTripleValue z')/Y)*
       OAI.Problem337.RealPhase.phase (θ*((markedMajorLabelTripleValue z-markedMajorLabelTripleValue z')/Y))) := by
  unfold markedMajorArcCharacterTerm
  simp_rw [markedMajor_bare_left_twist,markedMajor_bare_right_twist,
    markedMajorIntegerDeterminant_real,mul_div_assoc]

end
end ArtinMatthews
