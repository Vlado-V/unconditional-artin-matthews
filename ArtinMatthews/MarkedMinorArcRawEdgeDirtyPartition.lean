module

public import ArtinMatthews.MarkedMinorArcRawEdgeDirtyPieces
public import ArtinMatthews.MarkedMinorArcRawEdgePatternSymmetrized
public import ArtinMatthews.MarkedMinorArcRawEdgeJointReverse
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
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The actual endpoint errors remain explicit when the good projection
is removed.  Delta and major errors retain their own literal detectors. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeEndpointError {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (G : MarkedRawState P (pads+1) B Z → Prop) (A : MarkedRawEdgePatternKernel P pads B Z) :
    MarkedRawEdgePatternKernel P pads B Z :=
  (markedRawEdgeEndpointPiece G false false A + markedRawEdgeEndpointPiece G false true A) +
    markedRawEdgeEndpointPiece G true false A

theorem markedRawEdgeEndpointError_reverse {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (G : MarkedRawState P (pads+1) B Z → Prop) (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgePatternReverse (markedRawEdgeEndpointError G A) =
      markedRawEdgeEndpointError G (markedRawEdgePatternReverse A) := by
  funext p q s t
  by_cases hs : G s <;> by_cases ht : G t <;>
    simp [markedRawEdgePatternReverse,markedRawEdgeEndpointError,markedRawEdgeEndpointPiece,hs,ht]

theorem markedRawEdgeKernel_eq_good_add_error {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (G : MarkedRawState P (pads+1) B Z → Prop) (A : MarkedRawEdgePatternKernel P pads B Z) :
    A = markedRawEdgeEndpointPiece G true true A + markedRawEdgeEndpointError G A := by
  funext p q s t
  have h := markedRawEdgeEndpointPiece_partition G A p q s t
  simpa only [markedRawEdgeEndpointError,Pi.add_apply,add_assoc] using h

theorem markedRawEdgePatternApply_good_error {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (G : MarkedRawState P (pads+1) B Z → Prop) (A : MarkedRawEdgePatternKernel P pads B Z)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgePatternApply ν δ γ hZ A f =
      markedRawEdgePatternApply ν δ γ hZ (markedRawEdgeEndpointPiece G true true A) f +
        markedRawEdgePatternApply ν δ γ hZ (markedRawEdgeEndpointError G A) f := by
  conv_lhs => rw [markedRawEdgeKernel_eq_good_add_error G A]
  rw [markedRawEdgePatternApply_add]

theorem markedRawEdgePatternSymmetrized_good_error {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (G : MarkedRawState P (pads+1) B Z → Prop) (A : MarkedRawEdgePatternKernel P pads B Z)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgePatternSymmetrized ν δ γ hZ A f =
      markedRawEdgePatternSymmetrized ν δ γ hZ (markedRawEdgeEndpointPiece G true true A) f +
        markedRawEdgePatternSymmetrized ν δ γ hZ (markedRawEdgeEndpointError G A) f := by
  conv_lhs => rw [markedRawEdgeKernel_eq_good_add_error G A]
  rw [markedRawEdgePatternSymmetrized_add]

theorem markedRawEdgeJointCoefficient_eq_detector
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t =
      markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ (markedBanEdgeKernel ψ Q Y) s t := by
  rw [markedRawEdgeJointCoefficient_factor]
  unfold markedRawEdgeJointDetectorCoefficient
  dsimp only
  split_ifs <;> ring

theorem markedRawEdgeJointDetectorCoefficient_sub
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (η : ℝ → ℂ) (d₀ Y ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (D₁ D₂ : ℤ → ℤ → ℤ → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ (D₁-D₂) s t =
      markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D₁ s t -
        markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ D₂ s t := by
  unfold markedRawEdgeJointDetectorCoefficient
  dsimp only [Pi.sub_apply]
  split_ifs <;> ring

theorem markedRawEdgeJointCoefficient_delta_sub_major
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t =
      markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y) s t -
        markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeMajorDetector ψ Q Y) s t := by
  rw [markedRawEdgeJointCoefficient_eq_detector]
  have hD : markedBanEdgeKernel ψ Q Y = markedRawEdgeDeltaDetector ψ Y - markedRawEdgeMajorDetector ψ Q Y := by
    funext b a t
    dsimp only [markedBanEdgeKernel,markedRawEdgeDeltaDetector,markedRawEdgeMajorDetector,Pi.sub_apply]
    ring
  rw [hD,markedRawEdgeJointDetectorCoefficient_sub]

theorem markedRawDirtyJoint_good_delta_major_errors
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y Q ρ : ℝ) {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (w : Z → ℤ × ℤ) (χ : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z → ℂ)
    (p q : J → Bool) (s t : MarkedRawState (markedRawActualPrimeBand e x) (pads+1) B Z) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t =
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (markedRawDirtyGoodCutoff e x r d₀ Y w χ) s t +
      markedRawEdgeEndpointError (MarkedRawDirtyGood e x r d₀ Y w)
        (fun _ _ => markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)) p q s t -
      markedRawEdgeEndpointError (MarkedRawDirtyGood e x r d₀ Y w)
        (fun _ _ => markedRawEdgeJointDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeMajorDetector ψ Q Y)) p q s t := by
  simp only [markedRawEdgeJointCoefficient_delta_sub_major]
  rw [markedRawDirtyGood_joint_detector e x r d₀ Y ρ hZ w η χ (markedRawEdgeDeltaDetector ψ Y) p q,
    markedRawDirtyGood_joint_detector e x r d₀ Y ρ hZ w η χ (markedRawEdgeMajorDetector ψ Q Y) p q]
  by_cases hs : MarkedRawDirtyGood e x r d₀ Y w s <;>
    by_cases ht : MarkedRawDirtyGood e x r d₀ Y w t <;>
    simp [markedRawEdgeEndpointError,markedRawEdgeEndpointPiece,hs,ht]

end
end ArtinMatthews
