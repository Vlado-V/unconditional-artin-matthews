module

public import ArtinMatthews.MarkedPhysicalEdgeReindex
public import ArtinMatthews.MarkedPhysicalRootTargetReindex
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

/-! Exact coordinates of the original finite damped physical pairing.
All endpoint tests remain in the summand; the source residue modulus may
depend on the actual ordered union label. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalEdgePositionTerm {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    (a b : MarkedPhysicalMarking P (pads+1)) (z w : ℤ × ℤ) : ℂ :=
  if hz : z ∈ Z then if hw : w ∈ Z then
    markedPhysicalEdgePairTerm P hP V pads Z hZ ψ η d₀ Y Q q f g (⟨z,hz⟩,a) (⟨w,hw⟩,b)
  else 0 else 0

theorem markedPhysicalEdgePairing_positions {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      ∑ u : MarkedPhysicalMarking P (pads+2),∑ z ∈ Z,∑ w ∈ Z,
        markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
          (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u) z w := by
  rw [markedPhysicalEdgePairing_union_labels]
  apply Finset.sum_congr rfl
  intro u _
  let F := markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
    (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u)
  have hs : (∑ z : Z,∑ w : Z,F z.1 w.1) = ∑ z ∈ Z,∑ w ∈ Z,F z w := by
    calc
      _ = ∑ z : Z,∑ w ∈ Z,F z.1 w := by
        apply Finset.sum_congr rfl
        intro z _
        exact Finset.sum_coe_sort Z (F z.1)
      _ = _ := Finset.sum_coe_sort Z (fun z => ∑ w ∈ Z,F z w)
  rw [← hs]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  simp only [F,markedPhysicalEdgePositionTerm,dite_eq_left z.2,dite_eq_left w.2]

theorem markedPhysicalEdgePairing_root_coordinates
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ)
    (S : MarkedPhysicalMarking P (pads+2) → ℕ) [∀ u,NeZero (S u)]
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (hbox : Z ⊆ markedPhysicalPrimitiveBox A B C D) :
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      ∑ u : MarkedPhysicalMarking P (pads+2),
        ∑ r : MarkedPhysicalCanonicalRoot (S u) A B C D,
          ∑ z ∈ markedPhysicalCanonicalTargets hA hC r Z,
            markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
              (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u)
              (markedPhysicalCanonicalRootPosition r)
              ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z) := by
  rw [markedPhysicalEdgePairing_positions]
  apply Finset.sum_congr rfl
  intro u _
  let F := markedPhysicalEdgePositionTerm P hP V pads Z hZ ψ η d₀ Y Q q f g
    (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u)
  have hext : (∑ z ∈ Z,∑ w ∈ Z,F z w) =
      ∑ z ∈ markedPhysicalPrimitiveBox A B C D,∑ w ∈ Z,F z w := by
    apply Finset.sum_subset hbox
    intro z _ hz
    apply Finset.sum_eq_zero
    intro w _
    simp only [F,markedPhysicalEdgePositionTerm,dite_eq_right hz]
  rw [hext]
  have he := Equiv.sum_comp (markedPhysicalCanonicalRootEquiv (S := S u) (B := B) (D := D) hA hC)
    (fun z => ∑ w ∈ Z,F z.1 w)
  calc
    _ = ∑ z : ↥(markedPhysicalPrimitiveBox A B C D),∑ w ∈ Z,F z.1 w :=
      (Finset.sum_coe_sort _ (fun z => ∑ w ∈ Z,F z w)).symm
    _ = ∑ r : MarkedPhysicalCanonicalRoot (S u) A B C D,
        ∑ w ∈ Z,F (markedPhysicalCanonicalRootPosition r) w := he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      exact markedPhysicalCanonicalTargets_sum hA hC r Z (F (markedPhysicalCanonicalRootPosition r))

end ArtinMatthews
