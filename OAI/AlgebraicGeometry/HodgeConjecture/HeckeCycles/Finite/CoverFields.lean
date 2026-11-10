module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ConstructedCover
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


set_option backward.privateInPublic true
@[expose] public section

/-! # Cover Fields -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CoverFields.CM

noncomputable section

/-! Explicit field comparisons for the constructed finite cover,
including the harmless transport between index equality decisions. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BareNe.CM.Group
variable (I : Type*) [Fintype I] [d : DecidableEq I]

theorem action : (ConstructedCover.CM.finiteCover I).action = BareNe.CM.Group.bareAction := by
  have hd : d = Classical.decEq I := Subsingleton.elim _ _
  cases hd
  rfl

theorem projection_matrix (g : BareNe.CM.Group.BareGroup (I := I)) :
    ((ConstructedCover.CM.finiteCover I).project g).val = (BareNe.CM.Group.bareProjection g).val := by
  have hd : d = Classical.decEq I := Subsingleton.elim _ _
  cases hd
  rfl

theorem negOne : (ConstructedCover.CM.finiteCover I).negOne = BareNe.CM.Group.negOne := by
  have hd : d = Classical.decEq I := Subsingleton.elim _ _
  cases hd
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.CoverFields.CM
