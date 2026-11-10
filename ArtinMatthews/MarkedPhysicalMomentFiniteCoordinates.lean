module

public import ArtinMatthews.MarkedPhysicalMomentTube
public import ArtinMatthews.MarkedPhysicalPathCoordinateTerm
public import ArtinMatthews.MarkedPhysicalMomentCoordinateTube
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

/-! Exact finite enumeration for the genuine physical even moment:
fixed ordered labels and primitive relative coordinates precede the
canonical root/residue sum. All original weights and copies remain. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

def markedPhysicalMomentFiniteCoordinateSum
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ) (K U W : ℝ)
    (S : MarkedPhysicalLabelPath P (pads+1) (2*R) → ℕ) (hS : ∀ a,S a≠0) : ℂ :=
  ∑ a : MarkedPhysicalLabelPath P (pads+1) (2*R),
    letI : NeZero (S a) := ⟨hS a⟩
    ∑ tail : Fin (2*R) → ↥(markedPrimitiveCoordinateTube (markedPhysicalMomentTubeRadius (2*R) K (d₀*Y))),
      ∑ r : MarkedPhysicalCanonicalRoot (S a) U (16*U) W (2*W),
        markedPhysicalPathCoordinateTerm
          (markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R) a r (fun v => (tail v).1)

theorem markedPhysicalPositionMoment_finite_coordinates
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (hV : ∀ j,0≤V j) (R : ℕ) (hR : 0<R)
    (K U W : ℝ) (hd₀ : 0<d₀) (hY : 0<Y) (hK : 0≤K)
    (hψ : Function.support ψ ⊆ Set.Icc (-K) K) (hU : 1<U) (hW : 1<W)
    (hbox : Z⊆markedPhysicalPrimitiveBox U (16*U) W (2*W))
    (S : MarkedPhysicalLabelPath P (pads+1) (2*R) → ℕ) (hS : ∀ a,S a≠0) :
    markedPhysicalPositionMoment P (pads+1) Z V
      (markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G) R =
      markedPhysicalMass V (pads+1)*
        (markedPhysicalMomentFiniteCoordinateSum P hP V pads Z hZ ψ η d₀ Y Q q G R K U W S hS).re := by
  rw [markedPhysicalPositionMoment_residue_coordinates P hP V pads Z hZ ψ η d₀ Y Q q
    hdisj G hV R hR S hS hU hW hbox]
  congr 2
  unfold markedPhysicalPathResidueCoordinatesSum markedPhysicalMomentFiniteCoordinateSum
  apply Finset.sum_congr rfl
  intro a _
  let : NeZero (S a) := ⟨hS a⟩
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  exact markedPhysicalMomentCoordinateTube_sum P hP V pads Z hZ ψ η d₀ Y Q q
    G R a K hd₀ hY hK hψ hU hW hbox r

theorem markedPhysicalCanonicalRoot_sum_sigma {S : ℕ} [NeZero S] {A B C D : ℝ}
    (F : MarkedPhysicalCanonicalRoot S A B C D → ℂ) :
    (∑ r,F r)=
      ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        ∑ p : ↥(fixedURootMatrixBoxPoints g A B 0 1 C D true true true true true true),F ⟨g,p⟩ :=
  Fintype.sum_sigma _

end
end ArtinMatthews
