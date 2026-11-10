module

public import ArtinMatthews.GiantComparisonStripUnmasked
public import ArtinMatthews.GiantComparisonRestoredDamping
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! A comparison quotient can be summed first over its position, then
over its two distinct ordered free lists, and then over the admitted
copied lists. This preserves the original physical marking guards. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell N : ℕ}
  {C : J → Finset (Fin k)}

abbrev GiantComparisonSeparatedEdge (P : J → Finset ℕ) (C : J → Finset (Fin k))
    (ell N : ℕ) (aux : GiantTwoSidedPatternAuxiliary P C) :=
  Σ w : ↥(Ioc 0 N),
    Σ b : GiantComparisonFreeMarking P C ell w.val,
      Σ b' : GiantComparisonFreeMarking P C ell (w.val+giantTwoSidedPatternAuxiliaryProduct aux),
        {c : GiantComparisonSharedLabels P C // GiantComparisonSharedAdmissible aux c b.val b'.val}

def giantComparisonSeparatedEquiv (aux : GiantTwoSidedPatternAuxiliary P C) :
    GiantComparisonUnmaskedEdge P C ell N aux ≃ GiantComparisonSeparatedEdge P C ell N aux where
  toFun a :=
    ⟨a.val.2.1,
      ⟨a.val.2.2.1,
        fun j => ((giantComparisonJoinLabels_injective_iff a.val.1 a.val.2.2.1 j).mp
          (a.property.sourceDistinct j)).2.1,
        a.property.sourceDivides⟩,
      ⟨a.val.2.2.2,
        fun j => ((giantComparisonJoinLabels_injective_iff a.val.1 a.val.2.2.2 j).mp
          (a.property.targetDistinct j)).2.1,
        a.property.targetDivides⟩,
      ⟨a.val.1,a.property.sourceDistinct,a.property.targetDistinct,a.property.auxiliaryBan⟩⟩
  invFun a :=
    ⟨(a.2.2.2.val,a.1,a.2.1.val,a.2.2.1.val),
      a.2.2.2.property.1,a.2.2.2.property.2.1,a.2.1.property.2,a.2.2.1.property.2,
      mem_singleton_self _,mem_singleton_self _,a.2.2.2.property.2.2⟩
  left_inv a := Subtype.ext rfl
  right_inv a := by rcases a with ⟨w,b,b',c⟩; rfl

theorem giantComparisonRestoredSharedDamping_eq_sum [DecidableEq J]
    (aux : GiantTwoSidedPatternAuxiliary P C) (q : ℝ) (w w' : ℕ)
    (b b' : GiantComparisonFreeLabels P C ell) :
    giantComparisonRestoredSharedDamping aux q w w' b b' =
      ∑ c : {c : GiantComparisonSharedLabels P C // GiantComparisonSharedAdmissible aux c b b'},
        giantComparisonSharedMass c.val *
          ((giantTwoSidedEndpointDamping P (k+ell) q (giantComparisonSharedProduct c.val*w))^2 *
            (giantTwoSidedEndpointDamping P (k+ell) q (giantComparisonSharedProduct c.val*w'))^2) := by
  classical
  let good (c : GiantComparisonSharedLabels P C) := GiantComparisonSharedAdmissible aux c b b'
  let term (c : GiantComparisonSharedLabels P C) := giantComparisonSharedMass c *
    ((giantTwoSidedEndpointDamping P (k+ell) q (giantComparisonSharedProduct c*w))^2 *
      (giantTwoSidedEndpointDamping P (k+ell) q (giantComparisonSharedProduct c*w'))^2)
  have hs := Finset.sum_subtype (p := good) (F := inferInstance)
    (univ.filter good) (by simp) term
  change giantComparisonRestoredSharedDamping aux q w w' b b' = ∑ c : Subtype good,term c.val
  rw [← hs,sum_filter,giantComparisonRestoredSharedDamping]
  apply sum_congr rfl
  intro c _
  change giantComparisonSharedMass c*giantComparisonGuardedDamping aux q w w' b b' c =
    if good c then term c else 0
  split_ifs with hc
  · have hh : GiantComparisonSharedAdmissible aux c b b' := hc
    simp only [giantComparisonGuardedDamping, ite_eq_left hh, term]
  · have hh : ¬ GiantComparisonSharedAdmissible aux c b b' := hc
    simp only [giantComparisonGuardedDamping, ite_eq_right hh, mul_zero]

end
end ArtinMatthews
