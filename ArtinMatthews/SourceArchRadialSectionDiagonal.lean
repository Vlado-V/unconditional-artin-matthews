module

public import ArtinMatthews.SourceArchRadialFlow
public import ArtinMatthews.SourceArchRadialSection
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

/-! The literal upper-section radial curve is right diagonal multiplication. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

theorem sourceArchRadialFlow_section_diagonal (t : ℝ) (p : SourceArchUpperHalfSpace) :
    sourceArchRadialFlow t (sourceArchUpperHalfSection p) =
      sourceArchUpperHalfSection p * sourceArchPositiveDiagonal t := by
  have hz : sourceArchGramShift (sourceArchUpperHalfSection p) = p.1 :=
    congrArg Prod.fst (sourceArchGramCoordinates_section p)
  have hentry (i j : Fin 2) : sourceArchUpperHalfSection p i j =
      !![(Real.sqrt p.2.val : ℂ), p.1 / (Real.sqrt p.2.val : ℂ);
        0, (Real.sqrt p.2.val : ℂ)⁻¹] i j := rfl
  rw [sourceArchRadialFlow,hz]
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceArchRadialBorel_entry, sourceArchPositiveDiagonal, sourceKPDiagonalHom,
      hentry, Matrix.mul_apply, Fin.sum_univ_two,
      div_eq_mul_inv]
  all_goals ring

theorem sourceArchUpperHalfSection_diagonal_projective (t : ℝ) (p : SourceArchUpperHalfSpace) :
    ProjGenLinGroup.mk (sourceArchUpperHalfSection p * sourceArchPositiveDiagonal t) =
      ProjGenLinGroup.mk (sourceArchUpperHalfSection (sourceArchRadialPoint t p)) := by
  rw [← sourceArchRadialFlow_section_diagonal, sourceArchRadialFlow_section_projective]

end
end ArtinMatthews.SourceArchJacquet
