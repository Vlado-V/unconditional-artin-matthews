module

public import ArtinMatthews.MarkedPhysicalHilbertMatrix
public import ArtinMatthews.MarkedPhysicalRootCoordinates
public import ArtinMatthews.MarkedPhysicalEdgeKernelFormula
public import ArtinMatthews.MarkedPhysicalRawMatrixEntry
public import ArtinMatthews.MarkedRawGoodRootTransport
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

/-! The original physical complex edge weight at a fixed coordinate path
and ordered labels. Its entire archimedean kernel is root-independent;
the separate arithmetic q-hit factors are retained literally. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalCoordinateKernel {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (V : J → ℝ) (pads : ℕ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (source target : MarkedRawActive P (pads+1)) (z z' : ℤ × ℤ) : ℂ :=
  let b := ((markedRawActiveSplit pads) source).2
  let a := ((markedRawActiveSplit pads) target).2
  let D := markedRawCopiedProduct ((markedRawActiveSplit pads) source).1
  ((∏ j,(V j)⁻¹:ℝ):ℂ) *
    (if ((markedRawActiveSplit pads) source).1=((markedRawActiveSplit pads) target).1 then
      if d₀ ≤ (D:ℝ) ∧ (D:ℝ)<2*d₀ then
        if (D:ℤ) ∣ markedMinorIntegerDet z z' then
          if MarkedRawFullCrossBan source a then 0 else
            ((d₀/(D:ℝ):ℝ):ℂ)*η ((markedRawLastProduct b:ℝ)/Y)*η ((markedRawLastProduct a:ℝ)/Y)*
              markedBanEdgeKernel ψ Q Y (markedRawLastProduct b) (markedRawLastProduct a)
                (markedMinorIntegerDet z z'/(D:ℤ))
        else 0 else 0
    else 0)

theorem markedPhysicalEdgeMatrix_coordinate_kernel
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
    (V : J → ℝ) (hV : ∀ j,0<V j) (pads : ℕ)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z) (root completion z z' : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1)
    (hs : s.1.1.1=markedPhysicalRootLift root completion z)
    (ht : t.1.1.1=markedPhysicalRootLift root completion z') :
    markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q s t =
      (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1:ℂ)*
        markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q
          (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1
          (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1 z z' *
        (markedPhysicalEndpointDamping P (pads+1) q t.1.1.1:ℂ) := by
  rw [markedPhysicalEdgeMatrix_eq_raw P hP V hV pads Z hZ ψ η d₀ Y Q q s t]
  rw [markedPhysicalRawJointCoefficient_kernel P hP pads Z hZ ψ η d₀ Y Q s t]
  rw [hs,ht,markedPhysicalRootLift_det root completion z z' hdet]
  unfold markedPhysicalCoordinateKernel
  split_ifs <;> simp_all
  all_goals ring

theorem markedPhysicalCoordinateKernel_root_lift
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (V : J → ℝ) (pads : ℕ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (source target : MarkedRawActive P (pads+1)) (root completion z z' : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1) :
    markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q source target
      (markedPhysicalRootLift root completion z) (markedPhysicalRootLift root completion z') =
      markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q source target z z' := by
  unfold markedPhysicalCoordinateKernel
  rw [markedPhysicalRootLift_det root completion z z' hdet]

end ArtinMatthews
