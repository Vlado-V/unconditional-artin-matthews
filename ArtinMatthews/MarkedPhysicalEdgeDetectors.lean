module

public import ArtinMatthews.MarkedPhysicalGoodPairing
public import ArtinMatthews.MarkedMinorArcRawEdgeJointDetector
public import ArtinMatthews.MarkedMinorArcRawEdgeDirtyPartition
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

/-! The original physical determinant and major-arc pairings, with the
same ordered labels, copy condition, sigma mass and endpoint damping.
Their difference is exactly the already-defined minor-arc pairing. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalEdgeDetectorCoefficient
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η : ℝ → ℂ) (d₀ Y q : ℝ) (D : ℤ → ℤ → ℤ → ℂ)
    (s t : MarkedPhysicalState P (pads+1) Z) : ℂ :=
  let u := markedPhysicalStateToRaw P hP (pads+1) Z s
  let v := markedPhysicalStateToRaw P hP (pads+1) Z t
  ((markedPhysicalMass V (pads+1) * ∏ j, (V j)⁻¹ : ℝ) : ℂ) *
    (if ((markedRawActiveSplit pads) u.2.1).1 = ((markedRawActiveSplit pads) v.2.1).1 then
      (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1 : ℂ) *
        markedRawEdgeJointDetectorCoefficient hZ η d₀ Y 1 (fun _ => 1) D u v *
        (markedPhysicalEndpointDamping P (pads+1) q t.1.1.1 : ℂ)
    else 0)

def markedPhysicalEdgeDetectorPairing
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η : ℝ → ℂ) (d₀ Y q : ℝ) (D : ℤ → ℤ → ℤ → ℂ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) : ℂ :=
  ∑ s, ∑ t, markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ η d₀ Y q D s t *
    star (f s) * g t

theorem markedPhysicalEdgeCoefficient_eq_delta_sub_major
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t =
      markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ η d₀ Y q
        (markedRawEdgeDeltaDetector ψ Y) s t -
      markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ η d₀ Y q
        (markedRawEdgeMajorDetector ψ Q Y) s t := by
  unfold markedPhysicalEdgeCoefficient markedPhysicalEdgeDetectorCoefficient
  dsimp only
  rw [markedRawEdgeJointCoefficient_delta_sub_major]
  split_ifs <;> ring

theorem markedPhysicalEdgePairing_eq_delta_sub_major
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (f g : MarkedPhysicalState P (pads+1) Z → ℂ) :
    markedPhysicalEdgePairing P hP V pads Z hZ ψ η d₀ Y Q q f g =
      markedPhysicalEdgeDetectorPairing P hP V pads Z hZ η d₀ Y q
        (markedRawEdgeDeltaDetector ψ Y) f g -
      markedPhysicalEdgeDetectorPairing P hP V pads Z hZ η d₀ Y q
        (markedRawEdgeMajorDetector ψ Q Y) f g := by
  unfold markedPhysicalEdgePairing markedPhysicalEdgeDetectorPairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [markedPhysicalEdgeCoefficient_eq_delta_sub_major]
  ring

end ArtinMatthews
