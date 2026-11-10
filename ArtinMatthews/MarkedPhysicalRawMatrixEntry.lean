module

public import ArtinMatthews.MarkedPhysicalHilbertMatrix
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

/-! The actual physical row entry is the original constant atom times
the literal copied-prefix/raw joint coefficient and real q dampings. -/
namespace ArtinMatthews
open Matrix
open scoped BigOperators Classical
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedPhysicalEdgeMatrix_eq_raw
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ) (hV : ∀ j,0<V j)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    let u := markedPhysicalStateToRaw P hP (pads+1) Z s
    let v := markedPhysicalStateToRaw P hP (pads+1) Z t
    markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q s t =
      (∏ j,(V j)⁻¹ : ℝ) *
        (if ((markedRawActiveSplit pads) u.2.1).1=((markedRawActiveSplit pads) v.2.1).1 then
          (markedPhysicalEndpointDamping P (pads+1) q s.1.1.1:ℂ) *
            markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) u v *
            (markedPhysicalEndpointDamping P (pads+1) q t.1.1.1:ℂ)
        else 0) := by
  dsimp only
  have hσ : (markedPhysicalMass V (pads+1):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (markedPhysicalMass_pos V (pads+1) hV).ne'
  unfold markedPhysicalEdgeMatrix markedPhysicalEdgeCoefficient
  dsimp only
  apply (div_eq_iff hσ).mpr
  rw [Complex.ofReal_mul]
  ring

theorem markedPhysicalEdgeMatrix_ne_zero_guards
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
    (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z)
    (h : markedPhysicalEdgeMatrix P hP V pads Z hZ ψ η d₀ Y Q q s t≠0) :
    let u := markedPhysicalStateToRaw P hP (pads+1) Z s
    let v := markedPhysicalStateToRaw P hP (pads+1) Z t
    ((markedRawActiveSplit pads) u.2.1).1=((markedRawActiveSplit pads) v.2.1).1 ∧
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q 1 (fun _ => 1) u v≠0 := by
  dsimp only
  have hc : markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q s t≠0 := by
    intro hz
    exact h (by simp only [markedPhysicalEdgeMatrix,hz,zero_div])
  constructor
  · by_contra hn
    exact hc (by simp only [markedPhysicalEdgeCoefficient,ite_eq_right hn,mul_zero])
  · intro hz
    exact hc (by simp only [markedPhysicalEdgeCoefficient,hz,mul_zero,zero_mul,ite_self])

end
end ArtinMatthews
