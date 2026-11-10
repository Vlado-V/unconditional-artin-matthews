module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import OAI.RepresentationTheory.Weil.Local.FiniteSquareClasses
public import OAI.RepresentationTheory.Weil.Local.QuadraticNormSquareQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! # Quadratic Norm Index -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticNormIndex.Construction

noncomputable section

/-! The nonzero sums of two squares have index two when -1 is nonsquare over a nonarchimedean local field. -/

theorem localField_quadraticNorm_index_two
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (hnd : ¬ DiscreteTopology k) (h : ¬ ∃ t : k, t ^ 2 = -1) :
    (QuadraticNormSubgroup.Construction.quadraticNormSubgroup k).index = 2 := by
  have hi := Subgroup.relIndex_mul_index (QuadraticNormSubgroup.Construction.squareUnitsSubgroup_le_quadraticNormSubgroup (k := k))
  rw [QuadraticNormSquareQuotient.Construction.quadraticNorm_square_relIndex, FiniteSquareClasses.Construction.localField_square_index_eq_twice_normOne hnd h] at hi
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (FiniteSquareClasses.Construction.normOne_square_index_ne_zero hnd h))
  exact hi.trans (Nat.mul_comm _ _)

end

end OAI.RepresentationTheory.Weil.Local.QuadraticNormIndex.Construction
