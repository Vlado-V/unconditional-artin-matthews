module

public import ArtinMatthews.MarkedMinorArcRawEdgeCleanEnergy
public import ArtinMatthews.MarkedMinorArcRawEdgePatternPartition
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
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The patterned operator is the literal nonclean subtype sum. The
whole edge splits into its original clean and dirty actions before and
after the two genuine slot averages. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeDirtyApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ c : {c : MarkedRawEdgeChoice hZ s // ¬MarkedRawEdgeChoiceClean c},
    markedRawEdgeSummand ν V hZ ψ η d₀ Y Q ρ χ f s c.1

def markedRawEdgeSymmetrized {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) :=
  markedRawSlotAverage (markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ (markedRawSlotAverage f))

def markedRawEdgeCleanSymmetrized {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) :=
  markedRawSlotAverage (markedRawEdgeCleanApply ν V hZ ψ η d₀ Y Q ρ χ (markedRawSlotAverage f))

def markedRawEdgeDirtySymmetrized {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) :=
  markedRawSlotAverage (markedRawEdgeDirtyApply ν V hZ ψ η d₀ Y Q ρ χ (markedRawSlotAverage f))

theorem markedRawEdgeDirtyApply_eq_pattern {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeDirtyApply ν V hZ ψ η d₀ Y Q ρ χ f =
      markedRawEdgePatternApply ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (markedRawEdgeDirtyKernel (fun _ _ => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ)) f := by
  funext s
  unfold markedRawEdgeDirtyApply markedRawEdgePatternApply
  let F := markedRawEdgeSummand ν V hZ ψ η d₀ Y Q ρ χ f s
  have hsum : (∑ c : {c : MarkedRawEdgeChoice hZ s // ¬MarkedRawEdgeChoiceClean c},F c.1) =
      ∑ c : MarkedRawEdgeChoice hZ s,if ¬MarkedRawEdgeChoiceClean c then F c else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun c => ¬MarkedRawEdgeChoiceClean c)) (by simp) F).symm
  rw [hsum]
  apply Finset.sum_congr rfl
  intro c _
  rw [markedRawEdgeChoiceCharge_original]
  by_cases hc : MarkedRawEdgeChoiceClean c
  · have hk := (markedRawEdgeChoiceClean_iff_sector c).mp hc
    simp [markedRawEdgeDirtyKernel,markedRawEdgeFlagGate,hk,hc]
  · have hk : markedRawEdgeClassify (markedRawEdgeChoicePromoted c) c.store ≠ .clean := by
      intro h
      exact hc ((markedRawEdgeChoiceClean_iff_sector c).mpr h)
    simp only [hc,not_false_eq_true,ite_true,markedRawEdgeDirtyKernel,markedRawEdgeFlagGate]
    dsimp only [F,markedRawEdgeSummand]
    rw [markedRawEdgeChoiceCoefficient_eq_joint]
    rw [ite_eq_left hk]

theorem markedRawEdgeSymmetrized_eq_pattern {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y Q ρ χ f =
      markedRawEdgePatternSymmetrized ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (fun _ _ => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ) f := by
  unfold markedRawEdgeSymmetrized markedRawEdgePatternSymmetrized
  rw [markedRawEdgePatternApply_const,markedRawEdgeApply_eq_charged]

theorem markedRawEdgeDirtySymmetrized_eq_pattern {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeDirtySymmetrized ν V hZ ψ η d₀ Y Q ρ χ f =
      markedRawEdgePatternSymmetrized ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (markedRawEdgeDirtyKernel (fun _ _ => markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ)) f := by
  unfold markedRawEdgeDirtySymmetrized markedRawEdgePatternSymmetrized
  rw [markedRawEdgeDirtyApply_eq_pattern]

theorem markedRawEdgeApply_eq_clean_dirty_actions {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ f =
      markedRawEdgeCleanApply ν V hZ ψ η d₀ Y Q ρ χ f + markedRawEdgeDirtyApply ν V hZ ψ η d₀ Y Q ρ χ f := by
  funext s
  have h := markedRawEdgeApply_eq_clean_add_dirty ν V hZ ψ η d₀ Y Q ρ χ f s
  rw [← markedRawEdge_clean_sum ν V hZ ψ η d₀ Y Q ρ χ f s] at h
  exact h

theorem markedRawEdgeSymmetrized_eq_clean_add_dirty {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y Q ρ χ f =
      markedRawEdgeCleanSymmetrized ν V hZ ψ η d₀ Y Q ρ χ f +
        markedRawEdgeDirtySymmetrized ν V hZ ψ η d₀ Y Q ρ χ f := by
  unfold markedRawEdgeSymmetrized markedRawEdgeCleanSymmetrized markedRawEdgeDirtySymmetrized
  rw [markedRawEdgeApply_eq_clean_dirty_actions,markedRawSlotAverage_add]

end
end ArtinMatthews
