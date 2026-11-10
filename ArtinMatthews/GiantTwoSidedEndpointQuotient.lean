module

public import ArtinMatthews.GiantTwoSidedEndpointStates
public import ArtinMatthews.GiantCandidatePrimeStrip
public import ArtinMatthews.GiantCandidateAllocationParts
public import ArtinMatthews.MarkedPhysicalEndpointRecovery
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

/-! Dividing a represented position by its actual ordered list product
is injective at a fixed list. The stripped core part still divides the
quotient, even when the position has repeated active prime factors. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

def giantTwoSidedEndpointQuotient {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} {Z : Finset ℕ} (a : MarkedPhysicalMarking P M)
    (n : GiantTwoSidedEndpointPositions Z a) : ℕ :=
  n.1.val / markedPhysicalMarkingProduct a

theorem giantTwoSidedEndpointQuotient_mem {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) {M N : ℕ}
    {Z : Finset ℕ} (hZ : Z ⊆ Ioc 0 N) (a : MarkedPhysicalMarking P M)
    (n : GiantTwoSidedEndpointPositions Z a) :
    giantTwoSidedEndpointQuotient a n ∈ Ioc 0 (N/markedPhysicalMarkingProduct a) := by
  obtain ⟨hn0,hnN⟩ := mem_Ioc.mp (hZ n.1.property)
  have hd := markedPhysicalMarkingProduct_dvd hP hdis a n.2.1 n.2.2
  exact mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn0 hd) (markedPhysicalMarkingProduct_pos hP a),
    Nat.div_le_div_right hnN⟩

theorem giantTwoSidedEndpointQuotient_injective {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) {M : ℕ}
    {Z : Finset ℕ} (a : MarkedPhysicalMarking P M) :
    Function.Injective (giantTwoSidedEndpointQuotient (Z:=Z) a) := by
  intro n m he
  have hn := markedPhysicalMarkingProduct_dvd hP hdis a n.2.1 n.2.2
  have hm := markedPhysicalMarkingProduct_dvd hP hdis a m.2.1 m.2.2
  have h := congrArg (fun v => markedPhysicalMarkingProduct a * v) he
  apply Subtype.ext
  apply Subtype.ext
  simpa only [giantTwoSidedEndpointQuotient,Nat.mul_div_cancel' hn,Nat.mul_div_cancel' hm] using h

theorem giantCandidateStrip_dvd_markedQuotient {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) {M n : ℕ}
    (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    (hn : 0 < n) (hd : ∀ j k,(a j k:ℕ) ∣ n) :
    giantCandidateStrip (univ.biUnion P) n ∣ n / markedPhysicalMarkingProduct a := by
  let U := univ.biUnion P
  let D := markedPhysicalMarkingProduct a
  have hD : D ∣ n := markedPhysicalMarkingProduct_dvd hP hdis a ha hd
  have hU : D ∣ ∏ p ∈ U,p := by
    apply markedPhysicalMarkingProduct_dvd hP hdis a ha
    intro j k
    exact dvd_prod_of_mem (fun p : ℕ => p) (mem_biUnion.mpr ⟨j,mem_univ _,(a j k).2⟩)
  have hcop : (giantCandidateStrip U n).Coprime D :=
    (Nat.Coprime.of_dvd_left hU (giantCandidateStrip_coprime U hn.ne')).symm
  apply hcop.dvd_of_dvd_mul_left
  rw [Nat.mul_div_cancel' hD]
  exact giantCandidateStrip_dvd U n

end
end ArtinMatthews
