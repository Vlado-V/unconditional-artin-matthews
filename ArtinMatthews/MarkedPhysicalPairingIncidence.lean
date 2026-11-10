module

public import ArtinMatthews.MarkedPhysicalPairingCoordinates
public import ArtinMatthews.MarkedPhysicalActualLineMain
public import ArtinMatthews.MarkedPhysicalEndpointIncidence
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


set_option backward.privateInPublic true
@[expose] public section

/-! The original physical pairing in canonical root coordinates with its
actual distinct union labels and both endpoint line constraints retained. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalStateToRaw_cross_iff {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (pads : ℕ)
    (Z : Finset (ℤ × ℤ)) (s t : MarkedPhysicalState P (pads+1) Z) :
    MarkedRawFullCrossBan (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1
      ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1).2 ↔
    MarkedPhysicalCrossBan s.1.2 (markedPhysicalMarkingSplit pads t.1.2).2 := by
  constructor
  · rintro ⟨i,j,k,h⟩
    exact ⟨i,j,k,congrArg (fun p : Nat.Primes => (p : ℕ)) h⟩
  · rintro ⟨i,j,k,h⟩
    exact ⟨i,j,k,Subtype.ext h⟩

theorem markedPhysicalEdgePairTerm_ne_zero_distinct
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    (u : MarkedPhysicalMarking P (pads+2)) (z w : Z)
    (h : markedPhysicalEdgePairTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
      (z,markedPhysicalEdgeSource u) (w,markedPhysicalEdgeTarget u) ≠ 0) :
    MarkedPhysicalMarkingDistinct u := by
  unfold markedPhysicalEdgePairTerm markedPhysicalStateExtend at h
  split_ifs at h with hs ht
  · let s : MarkedPhysicalState P (pads+1) Z := ⟨(z,markedPhysicalEdgeSource u),hs⟩
    let t : MarkedPhysicalState P (pads+1) Z := ⟨(w,markedPhysicalEdgeTarget u),ht⟩
    have hc : markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t ≠ 0 := by
      intro hc
      exact h (by simp only [s,t,hc,zero_mul])
    have hb : ¬MarkedRawFullCrossBan (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1
        ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1).2 := by
      intro hb
      apply hc
      simp [markedPhysicalEdgeCoefficient,markedRawEdgeJointCoefficient,hb]
    have hp : ¬MarkedPhysicalCrossBan (markedPhysicalEdgeSource u)
        (markedPhysicalMarkingSplit pads (markedPhysicalEdgeTarget u)).2 :=
      fun hp => hb ((markedPhysicalStateToRaw_cross_iff P hP pads Z s t).mpr hp)
    have hu := (markedPhysicalEdgeUnion_distinct hdis (markedPhysicalEdgeSource u)
      (markedPhysicalEdgeTarget u)).mpr ⟨hs.2.1,hp⟩
    simpa only [markedPhysicalEdgeUnion_source_target] using hu
  · exact False.elim (h rfl)
  · exact False.elim (h rfl)

theorem markedPhysicalEdgePositionTerm_off_distinct
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    (u : MarkedPhysicalMarking P (pads+2)) (hu : ¬MarkedPhysicalMarkingDistinct u) (z w : ℤ × ℤ) :
    markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
      (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u) z w=0 := by
  by_contra h
  unfold markedPhysicalEdgePositionTerm at h
  split_ifs at h with hz hw
  · exact hu (markedPhysicalEdgePairTerm_ne_zero_distinct P hP hdis V pads Z hZ ψ η d₀ Y Q q f g u _ _ h)
  · exact h rfl
  · exact h rfl

theorem markedPhysicalEdgePositionTerm_incidence
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    (u : MarkedPhysicalMarking P (pads+2)) (hS : Squarefree (markedPhysicalMarkingProduct u))
    [NeZero (markedPhysicalMarkingProduct u)] {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D) (z : ℤ × ℤ) :
    (if markedPhysicalEdgeRootLineEvent u hS r.1 z then
      markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
        (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u)
        (markedPhysicalCanonicalRootPosition r) ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z)
      else 0) =
      markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
        (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u)
        (markedPhysicalCanonicalRootPosition r) ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z) := by
  by_cases he : markedPhysicalEdgeRootLineEvent u hS r.1 z
  · rw [ite_eq_left he]
  · rw [ite_eq_right he]
    symm
    by_contra hn
    apply he
    unfold markedPhysicalEdgePositionTerm at hn
    split_ifs at hn with hs ht
    · unfold markedPhysicalEdgePairTerm markedPhysicalStateExtend at hn
      split_ifs at hn with hsource htarget
      · exact markedPhysicalCanonicalRootLineEvent_of_endpoints hP u hS hA hC r z hsource htarget
      · exact False.elim (hn rfl)
      · exact False.elim (hn rfl)
    · exact False.elim (hn rfl)
    · exact False.elim (hn rfl)

def markedPhysicalCanonicalPairingSum
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C) : ℂ :=
  ∑ u : MarkedPhysicalMarking P (pads+2),
    if hu : MarkedPhysicalMarkingDistinct u then
      letI : NeZero (markedPhysicalMarkingProduct u) := ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
      let hS := markedPhysicalMarkingProduct_squarefree hP hdis u hu
      ∑ r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D,
        ∑ z ∈ markedPhysicalCanonicalTargets hA hC r Z,
          if markedPhysicalEdgeRootLineEvent u hS r.1 z then
            markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
              (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u)
              (markedPhysicalCanonicalRootPosition r) ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z)
          else 0
    else 0

theorem markedPhysicalEdgePairing_eq_canonical_sum
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (hbox : Z ⊆ markedPhysicalPrimitiveBox A B C D) :
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      markedPhysicalCanonicalPairingSum P hP hdis V pads Z hZ ψ η d₀ Y Q q f g
        (B := B) (D := D) hA hC := by
  let : ∀ u : MarkedPhysicalMarking P (pads+2),NeZero (markedPhysicalMarkingProduct u) :=
    fun u => ⟨(markedPhysicalMarkingProduct_pos hP u).ne'⟩
  rw [markedPhysicalEdgePairing_root_coordinates P hP V pads Z hZ ψ η d₀ Y Q q f g
    (fun u => markedPhysicalMarkingProduct u) hA hC hbox]
  unfold markedPhysicalCanonicalPairingSum
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : MarkedPhysicalMarkingDistinct u
  · rw [dite_eq_left hu]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro z _
    exact (markedPhysicalEdgePositionTerm_incidence P hP V pads Z hZ ψ η d₀ Y Q q f g u
      (markedPhysicalMarkingProduct_squarefree hP hdis u hu) hA hC r z).symm
  · rw [dite_eq_right hu]
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro z _
    exact markedPhysicalEdgePositionTerm_off_distinct P hP hdis V pads Z hZ ψ η d₀ Y Q q f g
      u hu _ _

end ArtinMatthews
