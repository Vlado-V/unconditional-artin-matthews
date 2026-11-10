module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.Jacobsthal.Harmonic.PolynomialStripPoints
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
public import OAI.NumberTheory.Jacobsthal.Paths.GlobalFiniteBranches


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

open Set
namespace ErdosRegularStrip
open ErdosImplicitCurvature ErdosLocalFiberGraphs ErdosGlobalFiberBranches ErdosConvexGraph

theorem regular_strip_lattice_bound (Q : Bivariate) (a b S : ℝ) (hS : 0 ≤ S)
    (hboundary : ∀ t ∈ Ioo a b, peval Q t 0 ≠ 0 ∧ peval Q t S ≠ 0)
    (hregular : ∀ t ∈ Ioo a b, ∀ y ∈ Icc 0 S, peval Q t y = 0 →
      peval (partialX Q) t y ≠ 0 ∧ peval (partialY Q) t y ≠ 0 ∧
        peval (inflectionPolynomial Q) t y ≠ 0) :
    ((polynomialStripPoints Q a b S).card : ℝ) ≤
      12*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by
  classical
  have hR : Ioo a b ⊆ regularParameters Q 0 S := by
    intro t ht
    exact ⟨(hboundary t ht).1,(hboundary t ht).2,
      fun y hy => (hregular t ht y hy.1 hy.2).2.1⟩
  obtain ⟨n,hn,f,hf,_,hvals,hcover⟩ :=
    global_branches_on_regular_domain Q 0 S (Ioo a b) isOpen_Ioo isPreconnected_Ioo hR
  have hcurve : ∀ i, ∀ t ∈ Ioo a b, peval Q t (f i t) = 0 :=
    fun i t ht => (hvals i t ht).2.1
  have hparts (i : Fin n) : ((graphLatticePoints (Ioo a b) (f i) S).card : ℝ) ≤
      12*(1+S^((2 : ℝ)/3)) := by
    apply regular_implicit_arc_lattice_bound Q (f i) a b S hS (hf i) (hcurve i)
    · intro t ht
      exact (hregular t ht (f i t) (Ioo_subset_Icc_self (hvals i t ht).1)
        (hcurve i t ht)).1
    · exact fun t ht => (hvals i t ht).2.2
    · intro t ht
      exact (hregular t ht (f i t) (Ioo_subset_Icc_self (hvals i t ht).1)
        (hcurve i t ht)).2.2
  have hcount : (polynomialStripPoints Q a b S).card ≤
      ∑ i : Fin n, (graphLatticePoints (Ioo a b) (f i) S).card := by
    rw [strip_eq_graph_union Q a b S f hcurve hcover]
    exact Finset.card_biUnion_le
  calc
    ((polynomialStripPoints Q a b S).card : ℝ) ≤
        ∑ i : Fin n, ((graphLatticePoints (Ioo a b) (f i) S).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _i : Fin n, 12*(1+S^((2 : ℝ)/3)) := Finset.sum_le_sum (fun i _ => hparts i)
    _ = (n : ℝ)*(12*(1+S^((2 : ℝ)/3))) := by simp
    _ ≤ (Q.totalDegree : ℝ)*(12*(1+S^((2 : ℝ)/3))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)
    _ = 12*(Q.totalDegree : ℝ)*(1+S^((2 : ℝ)/3)) := by ring

end ErdosRegularStrip

end

end Erdos970

end OAI
