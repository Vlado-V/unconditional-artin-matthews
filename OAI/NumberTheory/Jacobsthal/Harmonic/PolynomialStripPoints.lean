module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.Jacobsthal.Estimates.RegularImplicitArc
public import OAI.NumberTheory.Jacobsthal.Harmonic.PolynomialLocalGraph
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
public import Mathlib.Order.CompletePartialOrder
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

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosRegularStrip
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosConvexGraph
attribute [local instance] Classical.propDecidable

noncomputable def polynomialStripPoints (Q : Bivariate) (a b S : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) ⌊S⌋).product (Finset.Icc (0 : ℤ) ⌊S⌋)).filter
    (fun p => (p.1 : ℝ) ∈ Ioo a b ∧ peval Q p.1 p.2 = 0)

theorem mem_polynomialStripPoints (Q : Bivariate) (a b S : ℝ) (p : ℤ × ℤ) :
    p ∈ polynomialStripPoints Q a b S ↔
      InSquare S p ∧ (p.1 : ℝ) ∈ Ioo a b ∧ peval Q p.1 p.2 = 0 := by
  simp only [polynomialStripPoints,InSquare,Finset.mem_filter,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc,Int.le_floor,Int.cast_nonneg_iff]

theorem strip_eq_graph_union (Q : Bivariate) (a b S : ℝ) {n : ℕ} (f : Fin n → ℝ → ℝ)
    (hcurve : ∀ i, ∀ t ∈ Ioo a b, peval Q t (f i t) = 0)
    (hcover : ∀ t ∈ Ioo a b, boundedFiber Q t 0 S = range (fun i => f i t)) :
    polynomialStripPoints Q a b S =
      Finset.univ.biUnion (fun i => graphLatticePoints (Ioo a b) (f i) S) := by
  classical
  ext p
  constructor
  · intro hp
    have h := (mem_polynomialStripPoints Q a b S p).mp hp
    have hy : (p.2 : ℝ) ∈ boundedFiber Q p.1 0 S := ⟨h.1.2,h.2.2⟩
    obtain ⟨i,hi⟩ := (hcover p.1 h.2.1).subset hy
    apply Finset.mem_biUnion.mpr
    exact ⟨i,Finset.mem_univ i,(mem_graphLatticePoints _ _ _ p).mpr
      ⟨h.1,h.2.1,hi.symm⟩⟩
  · intro hp
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
    have h := (mem_graphLatticePoints (Ioo a b) (f i) S p).mp hi
    apply (mem_polynomialStripPoints Q a b S p).mpr
    refine ⟨h.1,h.2.1,?_⟩
    rw [h.2.2]
    exact hcurve i p.1 h.2.1

end ErdosRegularStrip

end

end Erdos970

end OAI
