module

public import ArtinMatthews.MarkedPhysicalEdgeDetectors
public import ArtinMatthews.MarkedPhysicalEdgeKernelFormula
public import ArtinMatthews.MarkedPhysicalEndpointDamping
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact arbitrary-detector physical coefficients and endpoint damping.
The original dyad, copied divisor and cross-edge ban remain literal. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p ∈ P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (η : ℝ → ℂ) (d₀ Y q : ℝ) (detector : ℤ → ℤ → ℤ → ℂ)

theorem markedPhysicalRawJointDetector_kernel
    (s t : MarkedPhysicalState P (pads+1) Z) :
    let u := markedPhysicalStateToRaw P hP (pads+1) Z s
    let v := markedPhysicalStateToRaw P hP (pads+1) Z t
    let b := ((markedRawActiveSplit pads) u.2.1).2
    let a := ((markedRawActiveSplit pads) v.2.1).2
    let D := markedRawCopiedProduct ((markedRawActiveSplit pads) u.2.1).1
    markedRawEdgeJointDetectorCoefficient hZ η d₀ Y 1 (fun _ => 1) detector u v=
      if d₀ ≤ (D:ℝ) ∧ (D:ℝ)<2*d₀ then
        if (D:ℤ) ∣ markedMinorIntegerDet s.1.1.1 t.1.1.1 then
          if MarkedRawFullCrossBan u.2.1 a then 0 else
            ((d₀/(D:ℝ):ℝ):ℂ)*η ((markedRawLastProduct b:ℝ)/Y)*η ((markedRawLastProduct a:ℝ)/Y)*
              detector (markedRawLastProduct b) (markedRawLastProduct a)
                (markedMinorIntegerDet s.1.1.1 t.1.1.1/(D:ℤ))
        else 0 else 0 := by
  dsimp only
  unfold markedRawEdgeJointDetectorCoefficient
  dsimp only
  rw [markedPhysicalRawEndpointFactor_one P hP (pads+1) Z hZ s,
    markedPhysicalRawEndpointFactor_one P hP (pads+1) Z hZ t]
  simp only [mul_one]
  rfl

theorem markedPhysicalEdgeDetectorCoefficient_kernel
    (s t : MarkedPhysicalState P (pads+1) Z) :
    let u := markedPhysicalStateToRaw P hP (pads+1) Z s
    let v := markedPhysicalStateToRaw P hP (pads+1) Z t
    let b := ((markedRawActiveSplit pads) u.2.1).2
    let a := ((markedRawActiveSplit pads) v.2.1).2
    let D := markedRawCopiedProduct ((markedRawActiveSplit pads) u.2.1).1
    markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ η d₀ Y q detector s t=
      (markedPhysicalMass V (pads+2):ℂ)*
        (if ((markedRawActiveSplit pads) u.2.1).1=((markedRawActiveSplit pads) v.2.1).1 then
          (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1:ℂ)*
            (if d₀ ≤ (D:ℝ) ∧ (D:ℝ)<2*d₀ then
              if (D:ℤ) ∣ markedMinorIntegerDet s.1.1.1 t.1.1.1 then
                if MarkedRawFullCrossBan u.2.1 a then 0 else
                  ((d₀/(D:ℝ):ℝ):ℂ)*η ((markedRawLastProduct b:ℝ)/Y)*η ((markedRawLastProduct a:ℝ)/Y)*
                    detector (markedRawLastProduct b) (markedRawLastProduct a)
                      (markedMinorIntegerDet s.1.1.1 t.1.1.1/(D:ℤ))
              else 0 else 0)*
            (markedPhysicalEndpointDamping P (pads+1) q t.1.1.1:ℂ)
        else 0) := by
  dsimp only
  unfold markedPhysicalEdgeDetectorCoefficient
  dsimp only
  rw [markedPhysicalRawJointDetector_kernel P hP pads Z hZ η d₀ Y detector s t,
    markedPhysicalMass_edge]

theorem markedPhysicalEdgeDetectorCoefficient_endpoint_damping (α β : ℕ → ℂ)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ η d₀ Y q detector s t*
      star (markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)*
      markedPhysicalEndpointVector P (pads+1) α β t.1.1.1=
    markedPhysicalEdgeDetectorCoefficient P hP V pads Z hZ η d₀ Y 1 detector s t*
      star (markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)*
      markedPhysicalEndpointVector P (pads+1) α β t.1.1.1 := by
  have hs : star (markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)*
      (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1:ℂ)=
      star (markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) := by
    simpa only [star_mul,Complex.star_def,Complex.conj_ofReal] using
      congrArg star (markedPhysicalEndpointVector_damped P (pads+1) q α β s.1.1.1)
  have ht := markedPhysicalEndpointVector_damped P (pads+1) q α β t.1.1.1
  have hd (z : ℤ × ℤ) : markedPhysicalEndpointDamping P (pads+1) 1 z=1 := by
    simp [markedPhysicalEndpointDamping]
  unfold markedPhysicalEdgeDetectorCoefficient
  dsimp only
  split_ifs
  · simp only [hd,Complex.ofReal_one,mul_one,one_mul]
    let c : ℂ := (markedPhysicalMass V (pads+1)*∏ j,(V j)⁻¹:ℝ)
    let k := markedRawEdgeJointDetectorCoefficient hZ η d₀ Y 1 (fun _ => 1) detector
      (markedPhysicalStateToRaw P hP (pads+1) Z s) (markedPhysicalStateToRaw P hP (pads+1) Z t)
    calc
      _ = c*k*(star (markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)*
          (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1:ℂ))*
          ((markedPhysicalEndpointDamping P (pads+1) q t.1.1.1:ℂ)*
            markedPhysicalEndpointVector P (pads+1) α β t.1.1.1) := by ring
      _ = _ := by rw [hs,ht]
  · simp

theorem markedPhysicalEdgeDetectorPairing_endpoint_damping (α β : ℕ → ℂ) :
    markedPhysicalEdgeDetectorPairing P hP V pads Z hZ η d₀ Y q detector
      (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)
      (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)=
    markedPhysicalEdgeDetectorPairing P hP V pads Z hZ η d₀ Y 1 detector
      (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1)
      (fun s => markedPhysicalEndpointVector P (pads+1) α β s.1.1.1) := by
  unfold markedPhysicalEdgeDetectorPairing
  exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ =>
    markedPhysicalEdgeDetectorCoefficient_endpoint_damping P hP V pads Z hZ η d₀ Y q detector α β s t))

end
end ArtinMatthews
