module

public import ArtinMatthews.MarkedMinorArcRawEdgeActualPartition
public import ArtinMatthews.MarkedMinorArcDirtyGoodCutoff
public import ArtinMatthews.MarkedMemoryGoodCutoff
public import ArtinMatthews.MarkedRawGoodSlots
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The computed good-cutoff edge is exactly G S T S G. The equality
uses the proved active-slot invariance of both literal good tests. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawGoodProjection {Ω : Type*} (G : Ω → Prop) (f : Ω → ℂ) : Ω → ℂ :=
  fun s => if G s then f s else 0

theorem markedRawSlotAverage_goodProjection
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (G : MarkedRawState P M B Z → Prop)
    (hG : ∀ σ s,G (markedRawSlotEquiv σ s) ↔ G s) (f : MarkedRawState P M B Z → ℂ) :
    markedRawSlotAverage (markedRawGoodProjection G f) =
      markedRawGoodProjection G (markedRawSlotAverage f) := by
  funext s
  unfold markedRawSlotAverage markedRawGoodProjection
  by_cases hs : G s
  · rw [ite_eq_left hs]
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    exact ite_eq_left ((hG σ s).mpr hs)
  · rw [ite_eq_right hs]
    have hz : (∑ σ : J → Equiv.Perm (Fin M),if G (markedRawSlotEquiv σ s) then f (markedRawSlotEquiv σ s) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro σ _
      exact ite_eq_right (fun h => hs ((hG σ s).mp h))
    rw [hz,mul_zero]

theorem markedRawEdgeApply_goodProjection
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) (G : MarkedRawState P (pads+1) B Z → Prop) :
    markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ (markedRawGoodProjection G χ) f =
      markedRawGoodProjection G
        (markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ (markedRawGoodProjection G f)) := by
  funext s
  unfold markedRawEdgeApply markedRawGoodProjection
  simp only [markedRawEdgeChoiceCoefficient_cutoff]
  by_cases hs : G s
  · rw [ite_eq_left hs]
    apply Finset.sum_congr rfl
    intro c _
    by_cases ht : G (markedRawEdgeTargetState hZ s c) <;> simp [hs,ht]
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro c _
    simp [hs]

theorem markedRawEdgeSymmetrized_goodProjection
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ f : MarkedRawState P (pads+1) B Z → ℂ) (G : MarkedRawState P (pads+1) B Z → Prop)
    (hG : ∀ σ s,G (markedRawSlotEquiv σ s) ↔ G s) :
    markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y Q ρ (markedRawGoodProjection G χ) f =
      markedRawGoodProjection G
        (markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y Q ρ χ (markedRawGoodProjection G f)) := by
  unfold markedRawEdgeSymmetrized
  rw [markedRawEdgeApply_goodProjection,markedRawSlotAverage_goodProjection G hG,
    ← markedRawSlotAverage_goodProjection G hG f]

theorem markedRawEdgeSymmetrized_actual_goodProjection
    {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ) (x : ℝ)
    (ν : (j : J) → ↥(markedRawActualPrimeBand e x j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ : ℝ) (w : Z → ℤ × ℤ)
    (χ f : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ) :
    markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y Q ρ (markedRawDirtyGoodCutoff e x r d₀ Y w χ) f =
      markedRawGoodProjection (MarkedRawDirtyGood e x r d₀ Y w)
        (markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y Q ρ χ
          (markedRawGoodProjection (MarkedRawDirtyGood e x r d₀ Y w) f)) := by
  have hcut : markedRawDirtyGoodCutoff e x r d₀ Y w χ =
      markedRawGoodProjection (MarkedRawDirtyGood e x r d₀ Y w) χ := by
    funext s
    exact markedRawDirtyGoodCutoff_eq_ite e x r d₀ Y w χ s
  rw [hcut]
  exact markedRawEdgeSymmetrized_goodProjection ν V hZ ψ η d₀ Y Q ρ χ f _
    (fun σ s => markedRawDirtyGood_slots e x r d₀ Y w s σ)

end
end ArtinMatthews
