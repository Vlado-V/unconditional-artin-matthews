module

public import ArtinMatthews.GiantTwoSidedResidueState
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Counting Haar coordinates gives the literal distinct ordered-list
reciprocal sum, including its original inverse band-mass normalization. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GiantTwoSidedResiduePositions {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M) :=
  {r : GiantTwoSidedFullResidue P // MarkedPhysicalMarkingDistinct a ∧
    ∀ j i,r (giantTwoSidedResidueIndex j (a j i))=0}

def giantTwoSidedResidueStatePositionsEquiv {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) :
    GiantTwoSidedResidueState P M ≃ Σ a : MarkedPhysicalMarking P M,
      GiantTwoSidedResiduePositions a where
  toFun s := ⟨s.val.2,s.val.1,s.property⟩
  invFun s := ⟨(s.2.val,s.1),s.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem giantTwoSidedResidue_incidence_iff {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M)
    (r : GiantTwoSidedFullResidue P) :
    (∀ j i,r (giantTwoSidedResidueIndex j (a j i))=0) ↔
      ∀ p : ↥(markedPhysicalBandPrimes P),p.val∈markedPhysicalActivePrimes a → r p=0 := by
  constructor
  · intro h p hp
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hp
    obtain ⟨i,_,hi⟩ := mem_image.mp hj
    have heq : giantTwoSidedResidueIndex j (a j i)=p := Subtype.ext hi
    exact heq ▸ h j i
  · intro h j i
    apply h
    exact mem_biUnion.mpr ⟨j,mem_univ _,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩

def giantTwoSidedResiduePositionsEquiv {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M)
    (ha : MarkedPhysicalMarkingDistinct a) :
    GiantTwoSidedResiduePositions a ≃
      ((p : ↥(markedPhysicalBandPrimes P)) →
        {z : ZMod p.val // p.val∈markedPhysicalActivePrimes a → z=0}) where
  toFun r p := ⟨r.val p,(giantTwoSidedResidue_incidence_iff a r.val).mp r.property.2 p⟩
  invFun r := ⟨fun p => (r p).val,ha,
    (giantTwoSidedResidue_incidence_iff a _).mpr (fun p => (r p).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem giantTwoSidedFullResidue_card {J : Type*} [Fintype J]
    (P : J → Finset ℕ) [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val] :
    Fintype.card (GiantTwoSidedFullResidue P)=∏ p∈markedPhysicalBandPrimes P,p := by
  rw [Fintype.card_pi]
  simp only [ZMod.card]
  exact prod_attach (markedPhysicalBandPrimes P) fun p => p

theorem giantTwoSidedResidueHaarStateMass_eq {J : Type*} [Fintype J]
    (P : J → Finset ℕ) [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val] (M : ℕ) :
    giantTwoSidedResidueHaarStateMass P M=
      markedPhysicalMass (fun j => bandReciprocalMass (P j)) M /
        Fintype.card (GiantTwoSidedFullResidue P) := by
  rw [giantTwoSidedResidueHaarStateMass,giantTwoSidedFullResidue_card]

theorem giantTwoSidedResiduePositions_card_mul {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M : ℕ}
    (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a) :
    Fintype.card (GiantTwoSidedResiduePositions a)*markedPhysicalMarkingProduct a=
      Fintype.card (GiantTwoSidedFullResidue P) := by
  have hcard : Fintype.card (GiantTwoSidedResiduePositions a)=
      ∏ p : ↥(markedPhysicalBandPrimes P),if p.val∈markedPhysicalActivePrimes a then 1 else p.val := by
    rw [Fintype.card_congr (giantTwoSidedResiduePositionsEquiv a ha),Fintype.card_pi]
    apply prod_congr rfl
    intro p _
    by_cases hp : p.val∈markedPhysicalActivePrimes a
    · simp [hp]
    · simp [hp,ZMod.card]
  have hprod : (∏ p∈markedPhysicalActivePrimes a,p)=markedPhysicalMarkingProduct a := by
    rw [markedPhysicalActivePrimes,prod_biUnion]
    · apply prod_congr rfl
      intro j _
      exact prod_image fun k _ l _ hkl => ha j (Subtype.ext hkl)
    · intro i _ j _ hij
      exact Disjoint.mono (markedPhysicalLabelSet_subset a i) (markedPhysicalLabelSet_subset a j) (hdis hij)
  have hactive : (∏ p : ↥(markedPhysicalBandPrimes P),
      if p.val∈markedPhysicalActivePrimes a then p.val else 1)=markedPhysicalMarkingProduct a := by
    rw [show (∏ p : ↥(markedPhysicalBandPrimes P),
      if p.val∈markedPhysicalActivePrimes a then p.val else 1)=
        ∏ p∈markedPhysicalBandPrimes P,if p∈markedPhysicalActivePrimes a then p else 1 from
          prod_attach (markedPhysicalBandPrimes P) (fun p => if p∈markedPhysicalActivePrimes a then p else 1)]
    rw [← hprod]
    symm
    calc
      _ = ∏ p∈markedPhysicalActivePrimes a,if p∈markedPhysicalActivePrimes a then p else 1 := by
        apply prod_congr rfl
        intro p hp
        exact (ite_eq_left hp).symm
      _ = _ := prod_subset (markedPhysicalActivePrimes_subset a) (fun p _ hp => ite_eq_right hp)
  rw [hcard,← hactive,← prod_mul_distrib,Fintype.card_pi]
  simp only [ZMod.card]
  apply prod_congr rfl
  intro p _
  by_cases hp : p.val∈markedPhysicalActivePrimes a <;> simp [hp]

theorem giantTwoSidedResiduePositions_mass {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M : ℕ}
    (a : MarkedPhysicalMarking P M) :
    giantTwoSidedResidueHaarStateMass P M*(Fintype.card (GiantTwoSidedResiduePositions a):ℝ)=
      if MarkedPhysicalMarkingDistinct a then
        markedPhysicalMass (fun j => bandReciprocalMass (P j)) M*markedPhysicalReciprocalProduct a
      else 0 := by
  by_cases ha : MarkedPhysicalMarkingDistinct a
  · rw [ite_eq_left ha,giantTwoSidedResidueHaarStateMass_eq,markedPhysicalReciprocalProduct_eq]
    have hprod : 0 < markedPhysicalMarkingProduct a :=
      prod_pos fun j _ => prod_pos fun i _ => (hP j _ (a j i).property).pos
    have hcard : 0<Fintype.card (GiantTwoSidedFullResidue P) := Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
    have heq : (Fintype.card (GiantTwoSidedResiduePositions a):ℝ)*(markedPhysicalMarkingProduct a:ℝ)=
        (Fintype.card (GiantTwoSidedFullResidue P):ℝ) := by
      exact_mod_cast giantTwoSidedResiduePositions_card_mul hdis a ha
    rw [div_mul_eq_mul_div,mul_one_div]
    apply (div_eq_div_iff (Nat.cast_ne_zero.mpr hcard.ne') (Nat.cast_ne_zero.mpr hprod.ne')).mpr
    rw [mul_assoc,heq]
  · have : IsEmpty (GiantTwoSidedResiduePositions a) := ⟨fun r => ha r.property.1⟩
    simp [ha]

theorem giantTwoSidedResidue_initialMass_eq {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (M : ℕ) :
    (∑ _s : GiantTwoSidedResidueState P M,giantTwoSidedResidueHaarStateMass P M)=
      ∑ a : MarkedPhysicalMarking P M,if MarkedPhysicalMarkingDistinct a then
        markedPhysicalMass (fun j => bandReciprocalMass (P j)) M*markedPhysicalReciprocalProduct a else 0 := by
  rw [(giantTwoSidedResidueStatePositionsEquiv P M).sum_comp (fun _ => giantTwoSidedResidueHaarStateMass P M)]
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro a _
  rw [sum_const,card_univ,nsmul_eq_mul,mul_comm]
  exact giantTwoSidedResiduePositions_mass hP hdis a

theorem giantTwoSidedResidue_initialMass_le_one {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j,0<bandReciprocalMass (P j)) (M : ℕ) :
    (∑ _s : GiantTwoSidedResidueState P M,giantTwoSidedResidueHaarStateMass P M)≤1 := by
  rw [giantTwoSidedResidue_initialMass_eq P hP hdis M]
  exact markedPhysicalMarking_distinct_normalized_sum_le_one P M hV

end
end ArtinMatthews
