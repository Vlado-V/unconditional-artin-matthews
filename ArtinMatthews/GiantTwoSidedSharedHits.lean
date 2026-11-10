module

public import ArtinMatthews.GiantTwoSidedEndpointStates
public import ArtinMatthews.MarkedPhysicalEndpointArithmetic
public import ArtinMatthews.GiantCandidateAllocationWeights
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Shared labels contribute their exact union with the existing active
divisors. The overlap count records every repeated active prime power
without counting its exponent as an extra mark. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantTwoSidedShared_activeDivisors_mul {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {k : ℕ} (c : MarkedPhysicalMarking P k) (j : J) (w : ℕ) :
    activeDivisors (P j) (markedPhysicalMarkingProduct c*w) =
      markedPhysicalLabelSet c j ∪ activeDivisors (P j) w := by
  ext p
  simp only [activeDivisors,mem_filter,mem_union]
  constructor
  · rintro ⟨hp,hd⟩
    have hprime := hP j p hp
    rcases hprime.dvd_mul.mp hd with hD | hw
    · left
      obtain ⟨i,l,he⟩ := (markedPhysicalMarkingProduct_prime_dvd_iff hP c hprime).mp hD
      have hji : j=i := by
        by_contra hn
        exact disjoint_left.mp (hdis hn) hp (he.symm ▸ (c i l).property)
      subst i
      exact mem_image.mpr ⟨l,mem_univ l,he.symm⟩
    · exact Or.inr ⟨hp,hw⟩
  · rintro (h | ⟨hp,hw⟩)
    · have hp := markedPhysicalLabelSet_subset c j h
      obtain ⟨l,_,he⟩ := mem_image.mp h
      have hD := (markedPhysicalMarkingProduct_prime_dvd_iff hP c (hP j p hp)).mpr ⟨j,l,he.symm⟩
      exact ⟨hp,dvd_mul_of_dvd_left hD w⟩
    · exact ⟨hp,dvd_mul_of_dvd_right hw _⟩

def giantTwoSidedSharedHits {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
    (c : MarkedPhysicalMarking P k) (w : ℕ) : ℕ :=
  ∑ j,(markedPhysicalLabelSet c j ∩ activeDivisors (P j) w).card

theorem giantTwoSidedShared_count_add {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {k : ℕ} (c : MarkedPhysicalMarking P k) (hc : MarkedPhysicalMarkingDistinct c) (w : ℕ) :
    bandCount (univ.biUnion P) (markedPhysicalMarkingProduct c*w) + giantTwoSidedSharedHits c w =
      k*Fintype.card J+bandCount (univ.biUnion P) w := by
  have hs : (∑ _j : J,k) = k*Fintype.card J := by simp [Nat.mul_comm]
  rw [giantCandidateBandCount_union P hdis (markedPhysicalMarkingProduct c*w),
    giantCandidateBandCount_union P hdis w,giantTwoSidedSharedHits,← hs,← sum_add_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  unfold bandCount
  rw [giantTwoSidedShared_activeDivisors_mul hP hdis c j w,
    card_union_add_card_inter,markedPhysicalLabelSet_card c hc j]

theorem giantTwoSidedSharedHits_le {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k : ℕ} (c : MarkedPhysicalMarking P k)
    (hc : MarkedPhysicalMarkingDistinct c) (w : ℕ) :
    giantTwoSidedSharedHits c w ≤ k*Fintype.card J := by
  unfold giantTwoSidedSharedHits
  have hs : (∑ _j : J,k) = k*Fintype.card J := by simp [Nat.mul_comm]
  rw [← hs]
  apply sum_le_sum
  intro j _
  exact (card_le_card inter_subset_left).trans_eq (markedPhysicalLabelSet_card c hc j)

theorem giantTwoSidedSharedHits_eq_zero_of_avoids {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k : ℕ} (c : MarkedPhysicalMarking P k) (w : ℕ)
    (hw : ∀ j l,¬(c j l:ℕ) ∣ w) :
    giantTwoSidedSharedHits c w = 0 := by
  unfold giantTwoSidedSharedHits
  apply sum_eq_zero
  intro j _
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨l,_,he⟩ := mem_image.mp (mem_inter.mp hp).1
  exact hw j l (he.symm ▸ (mem_filter.mp (mem_inter.mp hp).2).2)

theorem giantTwoSidedFree_count_le {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (b : (j : J) → ↥(P j)) {w : ℕ} (hb : ∀ j,(b j:ℕ) ∣ w) :
    Fintype.card J ≤ bandCount (univ.biUnion P) w := by
  let a : MarkedPhysicalMarking P 1 := fun j _ => b j
  have ha : MarkedPhysicalMarkingDistinct a := fun _ _ _ _ => Subsingleton.elim _ _
  simpa only [one_mul] using giantTwoSidedEndpoint_count_le hdis a ha (fun j _ => hb j)

theorem giantTwoSidedEndpointDamping_square {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M w : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (giantTwoSidedEndpointDamping P M q w)^2 =
      q^(bandCount (univ.biUnion P) w-M*Fintype.card J) := by
  let d := bandCount (univ.biUnion P) w-M*Fintype.card J
  change (q^((d:ℝ)/2))^2 = q^d
  rw [← Real.rpow_natCast (q^((d:ℝ)/2)) 2,← Real.rpow_mul hq]
  rw [show (d:ℝ)/2*((2:ℕ):ℝ)=(d:ℝ) by norm_num,Real.rpow_natCast]

theorem giantTwoSidedShared_damping_relation {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {k : ℕ} (c : MarkedPhysicalMarking P k) (hc : MarkedPhysicalMarkingDistinct c)
    (w : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hfull : (k+1)*Fintype.card J ≤ bandCount (univ.biUnion P) (markedPhysicalMarkingProduct c*w)) :
    (giantTwoSidedEndpointDamping P (k+1) q (markedPhysicalMarkingProduct c*w))^2 *
        q^(giantTwoSidedSharedHits c w) =
      (giantTwoSidedEndpointDamping P 1 q w)^2 := by
  have hc' := giantTwoSidedShared_count_add hP hdis c hc w
  have hsum : (bandCount (univ.biUnion P) (markedPhysicalMarkingProduct c*w) -
      (k+1)*Fintype.card J)+giantTwoSidedSharedHits c w =
        bandCount (univ.biUnion P) w-1*Fintype.card J := by
    simp only [Nat.add_mul,one_mul] at hfull ⊢
    omega
  rw [giantTwoSidedEndpointDamping_square P (k+1) _ hq,
    giantTwoSidedEndpointDamping_square P 1 _ hq,← pow_add,hsum]

theorem giantTwoSidedShared_damping_le {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    {k : ℕ} (c : MarkedPhysicalMarking P k) (hc : MarkedPhysicalMarkingDistinct c)
    (w : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hfull : (k+1)*Fintype.card J ≤ bandCount (univ.biUnion P) (markedPhysicalMarkingProduct c*w)) :
    (giantTwoSidedEndpointDamping P (k+1) q (markedPhysicalMarkingProduct c*w))^2 ≤
      (giantTwoSidedEndpointDamping P 1 q w)^2 * (q⁻¹)^(k*Fintype.card J) := by
  have h := giantTwoSidedShared_damping_relation hP hdis c hc w hq.le hfull
  calc
    _ = (giantTwoSidedEndpointDamping P 1 q w)^2 / q^(giantTwoSidedSharedHits c w) :=
      (eq_div_iff (pow_ne_zero _ hq.ne')).mpr h
    _ = (giantTwoSidedEndpointDamping P 1 q w)^2 * (q⁻¹)^(giantTwoSidedSharedHits c w) := by
      rw [div_eq_mul_inv,inv_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ ((one_le_inv₀ hq).mpr hq1) (giantTwoSidedSharedHits_le c hc w)) (sq_nonneg _)

end
end ArtinMatthews
