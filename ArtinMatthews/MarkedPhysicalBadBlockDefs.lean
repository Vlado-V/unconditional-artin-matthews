module

public import ArtinMatthews.MarkedPhysicalPairingCoordinates
public import ArtinMatthews.MarkedPhysicalSourceBad
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

/-! Literal canonical summands and their absolute finite block. Naming
these expressions keeps the coefficient opaque during bound elaboration. -/
noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalSourceBadTerm
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y Q : ℝ) (V : J → ℝ)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (w : Z → ℤ × ℤ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1))
    [NeZero (markedPhysicalMarkingProduct u)] (hS : Squarefree (markedPhysicalMarkingProduct u))
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C)
    (r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D) (z : ℤ × ℤ) : ℂ :=
  if markedPhysicalEdgeRootLineEvent u hS r.1 z then
    markedPhysicalEdgePositionTerm (fun j => markedLogPowerBand (e j) x)
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) V
      ⌊(Real.log x)^(1/100 : ℝ)⌋₊ Z hZ ψ η d₀ Y Q 1
      (markedPhysicalBadVector (MarkedPhysicalActualGood e x d₀ Y w) f) g
      (markedPhysicalEdgeSource u) (markedPhysicalEdgeTarget u)
      (markedPhysicalCanonicalRootPosition r) ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z)
  else 0

def markedPhysicalSourceBadBlock
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y Q : ℝ) (V : J → ℝ)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (w : Z → ℤ × ℤ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (f g : MarkedPhysicalState (fun j => markedLogPowerBand (e j) x) (markedPadSlots x) Z → ℂ)
    (u : MarkedPhysicalMarking (fun j => markedLogPowerBand (e j) x) (markedPadSlots x+1))
    [NeZero (markedPhysicalMarkingProduct u)] (hS : Squarefree (markedPhysicalMarkingProduct u))
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C) : ℝ :=
  ∑ r : MarkedPhysicalCanonicalRoot (markedPhysicalMarkingProduct u) A B C D,
    ∑ z ∈ markedPhysicalCanonicalTargets hA hC r Z,
      ‖markedPhysicalSourceBadTerm e x d₀ Y Q V Z hZ w ψ η f g u hS hA hC r z‖

end ArtinMatthews
