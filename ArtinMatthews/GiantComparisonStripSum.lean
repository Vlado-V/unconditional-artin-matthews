module

public import ArtinMatthews.GiantComparisonStripKernel
public import ArtinMatthews.GiantComparisonStripEquiv
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

/-! The physical double sum is supported on the exact comparison edges.
Taking its quotient reindexes the original auxiliary average unchanged. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell N m : ℕ}
  {C : J → Finset (Fin k)} {Z Z' : Finset ℕ}

theorem giantComparisonPhysical_sum_support (x q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (aux : GiantTwoSidedPatternAuxiliary P C) :
    (∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
      ∑ t : GiantTwoSidedEndpointState P (k+ell) Z',
        giantComparisonPhysicalSummand x q Ψ χ F G K s t aux) =
      ∑ e : GiantComparisonPhysicalEdge P C ell Z Z' aux,
        giantComparisonPhysicalSummand x q Ψ χ F G K e.val.1 e.val.2 aux := by
  classical
  let StatePair := GiantTwoSidedEndpointState P (k+ell) Z × GiantTwoSidedEndpointState P (k+ell) Z'
  let valid (p : StatePair) : Prop := GiantTwoSidedPatternCondition C 1 p.1 p.2 aux
  let term (p : StatePair) := giantComparisonPhysicalSummand x q Ψ χ F G K p.1 p.2 aux
  rw [← Fintype.sum_prod_type term]
  change (∑ p : StatePair, term p) = ∑ e : Subtype valid, term e.val
  have hs := Finset.sum_subtype (p := valid) (F := inferInstance)
    (univ.filter valid) (by simp) term
  rw [← hs, sum_filter]
  apply sum_congr rfl
  intro p _
  change term p = if valid p then term p else 0
  split_ifs with hp
  · rfl
  · have hn : ¬GiantTwoSidedPatternCondition C 1 p.1 p.2 aux := hp
    simp only [term, giantComparisonPhysicalSummand,
      giantTwoSidedPatternPhysicalCoefficient, ite_eq_right hn, mul_zero, zero_mul]

theorem giantComparisonPhysical_sum_eq_shared (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (hZ : Z ⊆ Ioc 0 N)
    {x : ℝ} (hx : 0 < x) (q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (hF : ∀ c : GiantComparisonSharedLabels P C, ∀ w : ℕ, 0 < w →
      F (giantComparisonSharedProduct c*w) = F w)
    (hG : ∀ c : GiantComparisonSharedLabels P C, ∀ w : ℕ, 0 < w →
      G (giantComparisonSharedProduct c*w) = G w)
    (hc : ∀ c : GiantComparisonSharedLabels P C, (giantComparisonSharedProduct c).Coprime m) :
    (∑ aux : GiantTwoSidedPatternAuxiliary P C,
      ∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
      ∑ t : GiantTwoSidedEndpointState P (k+ell) Z',
        giantComparisonPhysicalSummand x q Ψ χ F G K s t aux) =
      ∑ aux : GiantTwoSidedPatternAuxiliary P C,
      ∑ a : GiantComparisonSharedEdge P C ell N Z Z' aux,
        giantComparisonSharedSummand x q Ψ χ F G K a := by
  classical
  apply sum_congr rfl
  intro aux _
  rw [giantComparisonPhysical_sum_support]
  let term (e : GiantComparisonPhysicalEdge P C ell Z Z' aux) :=
    giantComparisonPhysicalSummand x q Ψ χ F G K e.val.1 e.val.2 aux
  change (∑ e, term e) = _
  rw [← (giantComparisonStripEquiv hP hdis hZ).symm.sum_comp term]
  apply sum_congr rfl
  intro a _
  have hw := (mem_Ioc.mp a.val.2.1.property).1
  exact giantComparisonPhysicalSummand_eq_shared hP hx q Ψ χ F G K a
    (hF a.val.1 _ hw) (hG a.val.1 _ (by omega)) (hc a.val.1)

end
end ArtinMatthews
