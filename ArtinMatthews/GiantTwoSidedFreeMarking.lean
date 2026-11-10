module

public import ArtinMatthews.GiantTwoSidedSharedDamping
public import ArtinMatthews.GiantCandidateAllocationWeights
public import ArtinMatthews.GiantTwoSidedSharedHits
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The remaining unshared labels enumerate the literal one-mark weight
on each stripped position, including the no-hit case. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GiantTwoSidedFreeMarking {J : Type*} (P : J → Finset ℕ) (w : ℕ) :=
  {b : (j : J) → ↥(P j) // ∀ j,(b j:ℕ) ∣ w}

def giantTwoSidedFreeMarkingEquiv {J : Type*} (P : J → Finset ℕ) (w : ℕ) :
    GiantTwoSidedFreeMarking P w ≃ ((j : J) → ↥(activeDivisors (P j) w)) where
  toFun b j := ⟨(b.1 j:ℕ),mem_filter.mpr ⟨(b.1 j).property,b.2 j⟩⟩
  invFun b := ⟨fun j => ⟨(b j:ℕ),(mem_filter.mp (b j).property).1⟩,
    fun j => (mem_filter.mp (b j).property).2⟩
  left_inv b := by apply Subtype.ext; funext j; rfl
  right_inv b := by funext j; rfl

theorem giantTwoSidedFreeMarking_card {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (w : ℕ) :
    Fintype.card (GiantTwoSidedFreeMarking P w) = ∏ j,bandCount (P j) w := by
  rw [Fintype.card_congr (giantTwoSidedFreeMarkingEquiv P w),Fintype.card_pi]
  simp only [Fintype.card_coe,bandCount]

theorem giantTwoSidedFreeMarking_weight_eq {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (w : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    ((Fintype.card (GiantTwoSidedFreeMarking P w):ℝ)*∏ j,(bandReciprocalMass (P j))⁻¹) *
      (giantTwoSidedEndpointDamping P 1 q w)^2 = giantCandidateActiveOneMark P q w := by
  rw [giantTwoSidedFreeMarking_card,Nat.cast_prod,giantTwoSidedEndpointDamping_square P 1 w hq]
  unfold giantCandidateActiveOneMark
  by_cases h : ∀ j,1 ≤ bandCount (P j) w
  · have hsum : (∑ j,(bandCount (P j) w-1)) + Fintype.card J = ∑ j,bandCount (P j) w := by
      have hJ : (∑ _j : J,(1:ℕ)) = Fintype.card J := by simp
      rw [← hJ,← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro j _
      exact Nat.sub_add_cancel (h j)
    have hexp : bandCount (univ.biUnion P) w-1*Fintype.card J = ∑ j,(bandCount (P j) w-1) := by
      rw [giantCandidateBandCount_union P hdis w,one_mul]
      omega
    rw [hexp,← prod_pow_eq_pow_sum]
    simp only [div_eq_mul_inv,prod_mul_distrib]
  · push Not at h
    obtain ⟨j,hj⟩ := h
    have hj0 : bandCount (P j) w=0 := by omega
    have h1 : (∏ j,(bandCount (P j) w:ℝ))=0 :=
      prod_eq_zero (mem_univ j) (by rw [hj0,Nat.cast_zero])
    have h2 : (∏ i,(bandCount (P i) w:ℝ)/bandReciprocalMass (P i)*q^(bandCount (P i) w-1))=0 :=
      prod_eq_zero (mem_univ j) (by rw [hj0,Nat.cast_zero,zero_div,zero_mul])
    rw [h1,h2,zero_mul,zero_mul]

theorem giantTwoSidedFreeMarking_pair_weight_eq {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (w : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (Fintype.card (GiantTwoSidedFreeMarking P w):ℝ)*
      (Fintype.card (GiantTwoSidedFreeMarking P (w+1)):ℝ)*
      (∏ j,(bandReciprocalMass (P j))⁻¹)^2*giantTwoSidedOneMarkDampingProduct P q w =
      giantCandidateActiveOneMark P q w*giantCandidateActiveOneMark P q (w+1) := by
  rw [← giantTwoSidedFreeMarking_weight_eq P hdis w hq,
    ← giantTwoSidedFreeMarking_weight_eq P hdis (w+1) hq,giantTwoSidedOneMarkDampingProduct]
  ring

end
end ArtinMatthews
