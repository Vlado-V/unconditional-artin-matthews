module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexTerm
public import ArtinMatthews.MarkedPhysicalMomentFiniteCoordinates
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

/-! All ordered marking, coordinate and slot-copy sums are assembled
on their literal finite product carrier before the canonical root sum. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

def markedPhysicalMomentIndexSum
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ) (K U W : ℝ)
    (S : MarkedPhysicalLabelPath P (pads+1) (2*R) → ℕ) (hS : ∀ a,S a≠0) : ℂ :=
  ∑ i : MarkedPhysicalCoordinateIndex P (pads+1) (2*R) (markedPhysicalMomentTubeRadius (2*R) K (d₀*Y)),
    letI : NeZero (S i.1) := ⟨hS i.1⟩
    ∑ r : MarkedPhysicalCanonicalRoot (S i.1) U (16*U) W (2*W),
      markedPhysicalCoordinateIndexTerm P hP V pads Z hZ ψ η d₀ Y Q q G i r

theorem markedPhysicalMomentFiniteCoordinateSum_eq_index
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ) (K U W : ℝ)
    (S : MarkedPhysicalLabelPath P (pads+1) (2*R) → ℕ) (hS : ∀ a,S a≠0) :
    markedPhysicalMomentFiniteCoordinateSum P hP V pads Z hZ ψ η d₀ Y Q q G R K U W S hS=
      markedPhysicalMomentIndexSum P hP V pads Z hZ ψ η d₀ Y Q q G R K U W S hS := by
  unfold markedPhysicalMomentFiniteCoordinateSum markedPhysicalMomentIndexSum
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  let : NeZero (S a) := ⟨hS a⟩
  apply Finset.sum_congr rfl
  intro tail _
  simp_rw [markedPhysicalMomentCoordinateTerm_sum_copies P hP V pads Z hZ ψ η d₀ Y Q q G R]
  exact Finset.sum_comm

theorem markedPhysicalPositionMoment_index_sum
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (hV : ∀ j,0≤V j) (R : ℕ) (hR : 0<R)
    (K U W : ℝ) (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) (hU : 1<U) (hW : 1<W)
    (hbox : Z⊆markedPhysicalPrimitiveBox U (16*U) W (2*W))
    (S : MarkedPhysicalLabelPath P (pads+1) (2*R) → ℕ) (hS : ∀ a,S a≠0) :
    markedPhysicalPositionMoment P (pads+1) Z V
      (markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G) R =
      markedPhysicalMass V (pads+1)*
        (markedPhysicalMomentIndexSum P hP V pads Z hZ ψ η d₀ Y Q q G R K U W S hS).re := by
  rw [markedPhysicalPositionMoment_finite_coordinates P hP V pads Z hZ ψ η d₀ Y Q q
    hdisj G hV R hR K U W hd₀ hY hK hψ hU hW hbox S hS,
    markedPhysicalMomentFiniteCoordinateSum_eq_index P hP V pads Z hZ ψ η d₀ Y Q q G R K U W S hS]

end
end ArtinMatthews
