module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.LinearAlgebra.Matrix.Reindex
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

/-! # Matrix Units Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatrixUnitsMap.CM

noncomputable section

/-! Map invertible matrices through coefficient homomorphisms and
coordinate equivalences, retaining both inverse matrices explicitly. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
variable {I J R S : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [CommRing R] [CommRing S]

def map (e : I ≃ J) (f : R →+* S) : (Matrix I I R)ˣ →* (Matrix J J S)ˣ :=
  Units.map ((f.mapMatrix.comp (Matrix.reindexRingEquiv R e).toRingHom).toMonoidHom)

theorem map_val (e : I ≃ J) (f : R →+* S) (A : (Matrix I I R)ˣ) (i j : J) :
    (CM.map e f A).val i j = f (A.val (e.symm i) (e.symm j)) := rfl

theorem map_inv_val (e : I ≃ J) (f : R →+* S) (A : (Matrix I I R)ˣ) (i j : J) :
    ((CM.map e f A)⁻¹).val i j = f ((A⁻¹).val (e.symm i) (e.symm j)) := by
  rw [← map_inv, map_val]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatrixUnitsMap.CM
