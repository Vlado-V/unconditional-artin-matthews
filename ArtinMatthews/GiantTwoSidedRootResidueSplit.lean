module

public import ArtinMatthews.GiantTwoSidedRootWeight
public import ArtinMatthews.GiantTwoSidedActiveResidueWeight
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

/-! The literal physical residue factor is its active-class indicator,
the fixed used-prime damping, and the full unused-prime product. The
used-prime damping is retained even when it is small. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedIntegerInactive_global {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M : ℕ} (labels : MarkedPhysicalMarking P M) (r : ℝ) (z : ℤ) :
    (∏ j,∏ p∈P j \ markedPhysicalLabelSet labels j,if (p:ℤ)∣z then r else 1) =
      ∏ p∈markedPhysicalBandPrimes P,
        if p∈markedPhysicalActivePrimes labels then 1 else if (p:ℤ)∣z then r else 1 := by
  unfold markedPhysicalBandPrimes
  rw [prod_biUnion (fun i _ j _ hij => hdis hij)]
  apply prod_congr rfl
  intro j _
  calc
    _ = ∏ p∈P j,if p∈markedPhysicalLabelSet labels j then 1
          else if (p:ℤ)∣z then r else 1 := by
      have he : (P j).filter (fun p => p∉markedPhysicalLabelSet labels j) =
          P j \ markedPhysicalLabelSet labels j := by
        ext p
        simp only [mem_filter,mem_sdiff]
      symm
      rw [prod_ite,prod_const_one,one_mul,he]
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      simp only [markedPhysicalActivePrimes_mem_group hdis labels j hp]

theorem giantTwoSidedRootResidueFactor_active {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ) (root : ℕ) :
    giantTwoSidedRootResidueFactor P labels q offset (root:ℤ) =
      if GiantTwoSidedActiveRoot univ labels offset root then
        ∏ p∈markedPhysicalBandPrimes P,
          giantTwoSidedIntegerPrimePath univ labels (markedMemoryVisitQ q n) offset root p
      else 0 := by
  have hindicator :
      (∏ v : Fin (n+1),∏ j,∏ p∈markedPhysicalLabelSet (labels v) j,
        if (p:ℤ)∣(root:ℤ)+offset v then (1:ℝ) else 0) =
        if GiantTwoSidedActiveRoot univ labels offset root then 1 else 0 := by
    by_cases ha : GiantTwoSidedActiveRoot univ labels offset root
    · rw [ite_eq_left ha]
      apply prod_eq_one
      intro v _
      apply prod_eq_one
      intro j _
      apply prod_eq_one
      intro p hp
      exact ite_eq_left (ha v (mem_univ v) p (mem_biUnion.mpr ⟨j,mem_univ j,hp⟩))
    · rw [ite_eq_right ha]
      unfold GiantTwoSidedActiveRoot at ha
      push Not at ha
      obtain ⟨v,_,p,hp,hd⟩ := ha
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp hp
      apply prod_eq_zero (mem_univ v)
      apply prod_eq_zero (mem_univ j)
      exact prod_eq_zero hj (ite_eq_right hd)
  have hinactive :
      (∏ v : Fin (n+1),∏ j,∏ p∈P j \ markedPhysicalLabelSet (labels v) j,
        if (p:ℤ)∣(root:ℤ)+offset v then markedMemoryVisitQ q n v else 1) =
        ∏ p∈markedPhysicalBandPrimes P,
          giantTwoSidedIntegerPrimePath univ labels (markedMemoryVisitQ q n) offset root p := by
    simp_rw [giantTwoSidedIntegerInactive_global hdis]
    rw [Finset.prod_comm]
    rfl
  unfold giantTwoSidedRootResidueFactor
  rw [prod_mul_distrib,hindicator,hinactive]
  split_ifs <;> simp only [one_mul,zero_mul]

theorem giantTwoSidedRootResidueFactor_forced {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ) (root : ℕ) :
    giantTwoSidedRootResidueFactor P labels q offset (root:ℤ) =
      if GiantTwoSidedActiveRoot univ labels offset root then
        giantTwoSidedActiveResidueWeight univ labels (markedMemoryVisitQ q n) offset *
          ∏ p∈markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes univ labels,
            (1-giantTwoSidedResidueLossNat univ (markedMemoryVisitQ q n) offset p (root%p))
      else 0 := by
  rw [giantTwoSidedRootResidueFactor_active hdis]
  split_ifs with h
  · exact giantTwoSidedIntegerPrimePath_forced_split univ labels (markedMemoryVisitQ q n) offset h
  · rfl

end
end ArtinMatthews
