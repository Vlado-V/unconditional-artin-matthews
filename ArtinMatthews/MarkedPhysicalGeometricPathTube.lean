module

public import ArtinMatthews.MarkedPhysicalCoordinatePathBounds
public import ArtinMatthews.MarkedPhysicalMomentGeometric
public import ArtinMatthews.MarkedPhysicalSlopeBandwidth
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The coordinate tube is derived from the literal alternating copy
support. Zero determinants and repeated physical positions are retained. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedRawEdgeAdjointCutoff_support (ψ : SchwartzMap ℝ ℂ) (K : ℝ)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) :
    Function.support (markedRawEdgeAdjointCutoff ψ) ⊆ Set.Icc (-K) K := by
  intro x hx
  have hn : ψ (-x) ≠ 0 := by
    intro hz
    exact hx (by simp only [markedRawEdgeAdjointCutoff_apply,hz,star_zero])
  have h := hψ hn
  constructor <;> linarith [h.1,h.2]

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q K : ℝ)

local notation "State" => MarkedPhysicalState P (pads+1) Z
local notation "Slots" => J → Equiv.Perm (Fin (pads+1))

theorem markedPhysicalMomentGeometricCopy_det_bound
    (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (j : ℕ) (s t : State) (c : Slots × Slots)
    (h : markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q j s t c≠0) :
    |(markedMinorIntegerDet s.1.1.1 t.1.1.1:ℝ)|≤2*K*(d₀*Y) := by
  by_cases hj : j%2=0
  · have hc : markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q q
        (markedPhysicalSlotEquiv P (pads+1) Z c.1 s)
        (markedPhysicalSlotEquiv P (pads+1) Z c.2 t)≠0 := by
      intro hz
      exact h (by simp only [markedPhysicalMomentGeometricCopy,hj,ite_true,
        markedPhysicalEdgeMatrix,hz,zero_div,mul_zero])
    simpa only [markedPhysicalSlotEquiv_position] using
      markedPhysicalEdgeCoefficient_det_bound P hP V pads Z hZ ψ η d₀ Y Q q K
        hd₀ hY hK hψ _ _ hc
  · have hc : markedPhysicalEdgeCoefficient P hP V pads Z hZ (markedRawEdgeAdjointCutoff ψ)
        (fun u => star (η u)) d₀ Y Q q
        (markedPhysicalSlotEquiv P (pads+1) Z c.1 s)
        (markedPhysicalSlotEquiv P (pads+1) Z c.2 t)≠0 := by
      intro hz
      exact h (by simp only [markedPhysicalMomentGeometricCopy,hj,ite_false,
        markedPhysicalEdgeMatrix,hz,zero_div,mul_zero])
    simpa only [markedPhysicalSlotEquiv_position] using
      markedPhysicalEdgeCoefficient_det_bound P hP V pads Z hZ (markedRawEdgeAdjointCutoff ψ)
        (fun u => star (η u)) d₀ Y Q q K hd₀ hY hK
        (markedRawEdgeAdjointCutoff_support ψ K hψ) _ _ hc

theorem markedPhysicalMomentGeometricPath_tube
    (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K)
    (n : ℕ) (p : Fin (n+1) → State) (copies : Fin n → Slots × Slots)
    (hsupport : ∀ k : Fin n,markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η
      d₀ Y Q q k.val (p k.castSucc) (p k.succ) (copies k)≠0)
    (completion : ℤ × ℤ) (hdet : markedMinorIntegerDet (p 0).1.1.1 completion=1)
    (U : ℝ) (hU : 0<U) (hbox : ∀ z∈Z,U≤(z.1:ℝ) ∧ (z.1:ℝ)≤16*U)
    (hr : ((completion.1:ℝ)/(p 0).1.1.1.1)∈Set.Icc (0:ℝ) 1) (v : Fin (n+1)) :
    |((markedPhysicalPathCoordinates (p 0).1.1.1 completion (fun k => (p k).1.1.1) v).1:ℝ)|
        ≤16+512*(n:ℝ)*K*(d₀*Y) ∧
      |((markedPhysicalPathCoordinates (p 0).1.1.1 completion (fun k => (p k).1.1.1) v).2:ℝ)|
        ≤512*(n:ℝ)*K*(d₀*Y) := by
  have hs (k : Fin n) :
      |(markedMinorIntegerDet (p k.castSucc).1.1.1 (p k.succ).1.1.1:ℝ)|≤2*K*(d₀*Y) :=
    markedPhysicalMomentGeometricCopy_det_bound P hP V pads Z hZ ψ η d₀ Y Q q K
      hd₀ hY hK hψ _ _ _ _ (hsupport k)
  have h := markedPhysicalPathCoordinates_tube completion (fun k => (p k).1.1.1)
    hdet U (2*K*(d₀*Y)) hU (by positivity)
    (fun k => hbox _ (p k).1.1.2) hs hr v
  have he : 256*(n:ℝ)*(2*K*(d₀*Y))=512*(n:ℝ)*K*(d₀*Y) := by ring
  simpa only [he] using h

end
end ArtinMatthews
