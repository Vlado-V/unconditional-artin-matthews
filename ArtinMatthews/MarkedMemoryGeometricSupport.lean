module

public import ArtinMatthews.MarkedMemoryBirthEventBoundary
public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedMemoryEndpointGuardData
public import ArtinMatthews.MarkedMemoryGeometricStage
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Only genuine support restrictions enter the oriented boundary sum.
The determinant gates imply anchor admissibility and the literal terminal
boundary implies empty pending memory; neither is assumed of all histories. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [decJ : DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

theorem markedMemoryGeometricHistoryWeight_anchor (offset : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s)
    (hw : markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n offset H≠0) :
    MarkedMemoryHistoryAnchorAdmissible hZ H := by
  rw [markedMemoryGeometricHistoryWeight_stage] at hw
  exact markedMemoryStageWeight_anchor hZ _ _ d₀ Y Q _ ν V ρ qStage n offset H hw

theorem markedMemoryGeometric_supported_boundary_sum
    (s : MarkedRawState P (pads+1) B Z) (z₀ : Z)
    (F : MarkedMemoryChronologicalHistory hZ n s → ℂ) :
    (∑ H : MarkedMemoryChronologicalHistory hZ n s,
      if MarkedMemoryHistoryBirthDistinct hZ H then
        markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n 0 H *
          markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H)*F H else 0)=
    ∑ H : MarkedMemoryPrimeSupportedHistory (n := n) hZ s,
      markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n 0 H.1 *
        markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H.1)*F H.1 := by
  let p := fun H : MarkedMemoryChronologicalHistory hZ n s =>
    MarkedMemoryHistoryAnchorAdmissible hZ H ∧ MarkedMemoryHistoryBirthDistinct hZ H ∧
      ∀ j,((markedMemoryChronologicalTarget hZ H).2.2.1.1 j:ℕ)=0
  let f := fun H : MarkedMemoryChronologicalHistory hZ n s =>
    if MarkedMemoryHistoryBirthDistinct hZ H then
      markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n 0 H *
        markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H)*F H else 0
  have hz : (∑ H : {H // ¬p H},f H.1)=0 := by
    apply Finset.sum_eq_zero
    intro H _
    by_cases ha : MarkedMemoryHistoryAnchorAdmissible hZ H.1
    · by_cases hd : MarkedMemoryHistoryBirthDistinct hZ H.1
      · have ht : ¬∀ j,((markedMemoryChronologicalTarget hZ H.1).2.2.1.1 j:ℕ)=0 :=
          fun ht => H.2 ⟨ha,hd,ht⟩
        have hm : (markedMemoryChronologicalTarget hZ H.1).2.2≠markedRawBoundaryEmptyMemory P B :=
          fun hm => ht ((markedMemoryRawMemory_empty_iff_sizes _).mp hm)
        simp only [f,hd,ite_true,markedRawBoundary,hm,and_false,ite_false,mul_zero,zero_mul]
      · simp only [f,hd,ite_false]
    · have hw : markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n 0 H.1=0 := by
        by_contra hw
        exact ha (markedMemoryGeometricHistoryWeight_anchor hZ ν V ψ η d₀ Y Q ρ orientation qStage χ 0 H.1 hw)
      simp only [f,hw,zero_mul,ite_self]
  have hs := Fintype.sum_subtype_add_sum_subtype p f
  rw [hz,add_zero] at hs
  have hh : (∑ H : {H // p H},f H.1)=
      ∑ H : {H // p H},
        markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n 0 H.1 *
          markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H.1)*F H.1 := by
    apply Finset.sum_congr rfl
    intro H _
    exact ite_eq_left H.2.2.1
  have hi (i₁ i₂ : Fintype (MarkedMemoryPrimeSupportedHistory (n := n) hZ s)) :
      @Finset.sum _ ℂ _ (@Finset.univ _ i₁) (fun H =>
        markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n 0 H.1 *
          markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H.1)*F H.1)=
      @Finset.sum _ ℂ _ (@Finset.univ _ i₂) (fun H =>
        markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n 0 H.1 *
          markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H.1)*F H.1) := by
    cases Subsingleton.elim i₁ i₂
    rfl
  exact hs.symm.trans (hh.trans (hi _ _))

def markedMemoryGeometricBoundarySourceValue (z₀ : Z)
    (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ H : MarkedMemoryChronologicalHistory hZ n s,
    if MarkedMemoryHistoryBirthDistinct hZ H then
      markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n 0 H *
        markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H) else 0

attribute [local irreducible] markedMemoryGeometricHistoryWeight markedMemoryGeometricBoundarySourceValue

theorem markedMemoryBirthDistinctGeometricBoundary_source (z₀ : Z) :
    markedMemoryBirthDistinctGeometricBoundaryPairing (N := n) ν V hZ ψ η d₀ Y Q ρ
      orientation qStage χ z₀=
      ∑ a : MarkedRawActive P (pads+1),
        (markedRawActiveMass ν a:ℂ)*
        markedMemoryGeometricBoundarySourceValue (n := n) hZ ν V ψ η d₀ Y Q ρ orientation qStage χ z₀
          (markedMemoryBoundarySource (B := B) z₀ a) := by
  cases Subsingleton.elim decJ (Classical.decEq J)
  have hsum : markedMemoryBirthDistinctGeometricBoundaryPairing (N := n) ν V hZ ψ η d₀ Y Q ρ
      orientation qStage χ z₀=
      ∑ s,(markedRawStateMass ν s:ℂ)*star (markedRawBoundary z₀ s)*
        markedMemoryGeometricBoundarySourceValue (n := n) hZ ν V ψ η d₀ Y Q ρ orientation qStage χ z₀ s := by
    unfold markedMemoryBirthDistinctGeometricBoundaryPairing
    apply Finset.sum_congr rfl
    intro s _
    unfold markedMemoryGeometricBoundarySourceValue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H _
    by_cases hd : MarkedMemoryHistoryBirthDistinct hZ H
    · simp only [hd,ite_true,markedMemoryGeometricBoundaryHistoryTerm]
      ring
    · simp only [hd,ite_false,mul_zero]
  exact hsum.trans (markedMemorySourceBoundary_sum ν z₀
    (markedMemoryGeometricBoundarySourceValue (n := n) hZ ν V ψ η d₀ Y Q ρ orientation qStage χ z₀))

theorem markedMemoryBirthDistinctGeometricBoundary_supported (z₀ : Z) :
    markedMemoryBirthDistinctGeometricBoundaryPairing (N := n) ν V hZ ψ η d₀ Y Q ρ
      orientation qStage χ z₀=
      ∑ a : MarkedRawActive P (pads+1),
        (markedRawStateMass ν (markedMemoryBoundarySource (B := B) z₀ a):ℂ)*
        ∑ H : MarkedMemoryPrimeSupportedHistory (n := n) hZ (markedMemoryBoundarySource (B := B) z₀ a),
          markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n 0 H.1 *
            markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ H.1) := by
  apply (markedMemoryBirthDistinctGeometricBoundary_source hZ ν V ψ η d₀ Y Q ρ orientation qStage χ z₀).trans
  apply Finset.sum_congr rfl
  intro a _
  rw [markedMemoryBoundarySource_mass]
  have hh := markedMemoryGeometric_supported_boundary_sum (n := n) hZ ν V ψ η d₀ Y Q ρ orientation qStage χ
    (markedMemoryBoundarySource (B := B) z₀ a) z₀ (fun _ => 1)
  simpa only [markedMemoryGeometricBoundarySourceValue,mul_one] using
    congrArg (fun z : ℂ => (markedRawActiveMass ν a:ℂ)*z) hh

end
end ArtinMatthews
