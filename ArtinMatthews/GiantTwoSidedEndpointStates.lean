module

public import ArtinMatthews.MarkedPhysicalMarking
public import ArtinMatthews.GiantCandidateAllocationWeights
public import ArtinMatthews.MarkedPhysicalEndpointArithmetic
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

/-! The positive-position slice of the two-sided graph has the original
ordered, distinct, represented lists. Its constant state mass and extra
half-damping are exactly those used in the endpoint norm. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GiantTwoSidedEndpointState {J : Type*} (P : J → Finset ℕ) (M : ℕ) (Z : Finset ℕ) :=
  {s : Z × MarkedPhysicalMarking P M // MarkedPhysicalMarkingDistinct s.2 ∧
    ∀ j k, (s.2 j k:ℕ) ∣ s.1.val}

abbrev GiantTwoSidedEndpointPositions {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (Z : Finset ℕ) (a : MarkedPhysicalMarking P M) :=
  {n : Z // MarkedPhysicalMarkingDistinct a ∧ ∀ j k,(a j k:ℕ) ∣ n.val}

def giantTwoSidedEndpointStatePositionsEquiv {J : Type*}
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset ℕ) :
    GiantTwoSidedEndpointState P M Z ≃ Σ a : MarkedPhysicalMarking P M,
      GiantTwoSidedEndpointPositions Z a where
  toFun s := ⟨s.1.2,s.1.1,s.2⟩
  invFun s := ⟨(s.2.1,s.1),s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def giantTwoSidedEndpointDamping {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (q : ℝ) (n : ℕ) : ℝ :=
  q^(((bandCount (univ.biUnion P) n-M*Fintype.card J:ℕ):ℝ)/2)

theorem giantTwoSidedEndpoint_count_le {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M n : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    (hd : ∀ j k, (a j k:ℕ) ∣ n) :
    M*Fintype.card J ≤ bandCount (univ.biUnion P) n := by
  have hcard (j : J) : M ≤ bandCount (P j) n := by
    have hs : markedPhysicalLabelSet a j ⊆ activeDivisors (P j) n := by
      intro p hp
      obtain ⟨k,_,rfl⟩ := mem_image.mp hp
      exact mem_filter.mpr ⟨(a j k).2,hd j k⟩
    simpa only [markedPhysicalLabelSet_card a ha j,bandCount] using card_le_card hs
  rw [giantCandidateBandCount_union P hdis n]
  calc
    _ = ∑ _j : J,M := by simp [Nat.mul_comm]
    _ ≤ _ := sum_le_sum (fun j _ => hcard j)

theorem giantTwoSidedEndpointDamping_eq_real {J : Type*} [Fintype J]
    {P : J → Finset ℕ} (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {M n : ℕ} (a : MarkedPhysicalMarking P M) (ha : MarkedPhysicalMarkingDistinct a)
    (hd : ∀ j k, (a j k:ℕ) ∣ n) (q : ℝ) :
    giantTwoSidedEndpointDamping P M q n =
      q^(((bandCount (univ.biUnion P) n:ℝ)-(M:ℝ)*Fintype.card J)/2) := by
  unfold giantTwoSidedEndpointDamping
  rw [Nat.cast_sub (giantTwoSidedEndpoint_count_le hdis a ha hd),Nat.cast_mul]

theorem giantTwoSidedEndpointDamping_mem_unitInterval {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    giantTwoSidedEndpointDamping P M q n ∈ Set.Icc (0:ℝ) 1 := by
  unfold giantTwoSidedEndpointDamping
  exact ⟨Real.rpow_nonneg hq.1 _,Real.rpow_le_one hq.1 hq.2 (by positivity)⟩

def giantTwoSidedEndpointEnergy {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset ℕ) (q : ℝ) (F : ℕ → ℂ) : ℝ :=
  ∑ s : GiantTwoSidedEndpointState P M Z,
    markedPhysicalMass (fun j => bandReciprocalMass (P j)) M *
      ‖(giantTwoSidedEndpointDamping P M q s.1.1.val:ℂ)*F s.1.1.val‖^2

def giantTwoSidedEndpointNorm {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset ℕ) (q : ℝ) (F : ℕ → ℂ) : ℝ :=
  Real.sqrt (giantTwoSidedEndpointEnergy P M Z q F)

theorem giantTwoSidedEndpointEnergy_eq_positions {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset ℕ) (q : ℝ) (F : ℕ → ℂ) :
    giantTwoSidedEndpointEnergy P M Z q F =
      ∑ a : MarkedPhysicalMarking P M, markedPhysicalMass (fun j => bandReciprocalMass (P j)) M *
        ∑ n : GiantTwoSidedEndpointPositions Z a,
          ‖(giantTwoSidedEndpointDamping P M q n.1.val:ℂ)*F n.1.val‖^2 := by
  classical
  unfold giantTwoSidedEndpointEnergy
  have he := (giantTwoSidedEndpointStatePositionsEquiv P M Z).sum_comp
    (fun t : Σ a : MarkedPhysicalMarking P M,GiantTwoSidedEndpointPositions Z a =>
      markedPhysicalMass (fun j => bandReciprocalMass (P j)) M *
        ‖(giantTwoSidedEndpointDamping P M q t.2.1.val:ℂ)*F t.2.1.val‖^2)
  simpa only [giantTwoSidedEndpointStatePositionsEquiv,Equiv.coe_fn_mk,Fintype.sum_sigma,
    ← Finset.mul_sum] using he

end
end ArtinMatthews
