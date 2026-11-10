module

public import ArtinMatthews.MarkedPhysicalCoordinateCopies
public import ArtinMatthews.MarkedPhysicalPathArrays
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

/-! The fixed-coordinate copy coefficient depends only on the original
ordered label arrays and slot permutations, rather than the lifted root. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ) (pads : ℕ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

def markedPhysicalCoordinateLabelCopy (j : ℕ)
    (a b : MarkedPhysicalMarking P (pads+1))
    (c : (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (z z' : ℤ × ℤ) : ℂ :=
  ((Fintype.card (J → Equiv.Perm (Fin (pads+1))):ℂ)⁻¹)^2 *
    (if j%2=0 then markedPhysicalCoordinateKernel V pads ψ η d₀ Y Q
      else markedPhysicalCoordinateKernel V pads (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u)) d₀ Y Q)
      ((markedPhysicalMarkingEquiv P hP (pads+1)).symm (fun i k => a i (c.1 i k)))
      ((markedPhysicalMarkingEquiv P hP (pads+1)).symm (fun i k => b i (c.2 i k))) z z'

theorem markedPhysicalCoordinateCopy_eq_labels (Z : Finset (ℤ × ℤ))
    (j : ℕ) (s t : MarkedPhysicalState P (pads+1) Z)
    (c : (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (z z' : ℤ × ℤ) :
    markedPhysicalCoordinateCopy P hP V pads Z ψ η d₀ Y Q j s t c z z' =
      markedPhysicalCoordinateLabelCopy P hP V pads ψ η d₀ Y Q j s.1.2 t.1.2 c z z' := rfl

theorem markedPhysicalMomentCopies_eq_label_coordinate
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (hV : ∀ j,0<V j)
    (q : ℝ) (n : ℕ) (pos : MarkedPhysicalPositionPath Z n)
    (a : MarkedPhysicalLabelPath P (pads+1) n) (ha : MarkedPhysicalPathArrayValid pos a)
    (copies : Fin n → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))))
    (root completion : ℤ × ℤ) (z : Fin (n+1) → ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1)
    (hpos : ∀ v,(pos v).1=markedPhysicalRootLift root completion (z v)) :
    (∏ v : Fin n,markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q v.val
      (markedPhysicalPathOfArrays pos a ha v.castSucc) (markedPhysicalPathOfArrays pos a ha v.succ) (copies v)) =
    (∏ v : Fin n,(markedPhysicalEndpointDamping P (pads+1) q (pos v.castSucc).1:ℂ)*
      (markedPhysicalEndpointDamping P (pads+1) q (pos v.succ).1:ℂ)) *
    ∏ v : Fin n,markedPhysicalCoordinateLabelCopy P hP V pads ψ η d₀ Y Q v.val
      (a v.castSucc) (a v.succ) (copies v) (z v.castSucc) (z v.succ) := by
  rw [markedPhysicalMomentGeometricCopies_coordinate P hP V pads Z ψ η d₀ Y Q
    hZ hV q n (markedPhysicalPathOfArrays pos a ha) copies root completion z hdet hpos]
  rfl

end
end ArtinMatthews
