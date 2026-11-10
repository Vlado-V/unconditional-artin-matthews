module

public import ArtinMatthews.GiantTwoSidedRootClass
public import ArtinMatthews.ScalarWeightedBonferroni
public import ArtinMatthews.GiantTwoSidedActiveResidueWeight
public import ArtinMatthews.GiantTwoSidedRootWeight
public import ArtinMatthews.GiantTwoSidedRootResidueSplit
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

/-! The original path-residue sum is exactly the weighted scalar CRT
count, with all deterministic active-prime factors retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedRootResidue_sum_eq_count {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ)
    (hc : GiantTwoSidedActiveCompatible univ labels offset) (lo hi : ℕ) :
    (∑ root∈Ico lo hi,giantTwoSidedRootResidueFactor P labels q offset (root:ℤ)) =
      giantTwoSidedActiveResidueWeight univ labels (markedMemoryVisitQ q n) offset *
        scalarWeightedResidueCountIco
          (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes univ labels)
          (giantTwoSidedResidueLossNat univ (markedMemoryVisitQ q n) offset)
          lo hi (giantTwoSidedActiveModulus labels) (giantTwoSidedRootClass hP labels offset) := by
  simp_rw [giantTwoSidedRootResidueFactor_forced hdis,
    giantTwoSidedActiveRoot_iff_class hP labels offset hc]
  unfold scalarWeightedResidueCountIco scalarWeightedResidueLoss
  rw [sum_filter,mul_sum]
  apply sum_congr rfl
  intro root _
  split_ifs <;> simp only [mul_zero]

theorem giantTwoSidedRootResidue_sum_incompatible {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ)
    (hc : ¬GiantTwoSidedActiveCompatible univ labels offset) (lo hi : ℕ) :
    (∑ root∈Ico lo hi,giantTwoSidedRootResidueFactor P labels q offset (root:ℤ))=0 := by
  apply sum_eq_zero
  intro root _
  rw [giantTwoSidedRootResidueFactor_active hdis,
    ite_eq_right (giantTwoSidedActiveRoot_impossible univ labels offset hc root)]

end
end ArtinMatthews
