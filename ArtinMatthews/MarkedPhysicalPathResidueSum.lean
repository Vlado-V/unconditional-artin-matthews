module

public import ArtinMatthews.MarkedPhysicalPositionRootReindex
public import ArtinMatthews.MarkedPhysicalMomentGeometric
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

/-! Exact ordered physical path enumeration with a modulus chosen after
fixing all label arrays. The original path weight is left literal. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section
attribute [local instance] markedPhysicalMomentFintype markedPhysicalMomentDecidableEq

def markedPhysicalPathResidueCoordinatesSum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (n : ℕ)
    (S : MarkedPhysicalLabelPath P M n → ℕ) (hS : ∀ a,S a≠0)
    {A B C D : ℝ} (hA : 1<A) (hC : 1<C)
    (F : (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ) : ℂ :=
  ∑ a : MarkedPhysicalLabelPath P M n,
    letI : NeZero (S a) := ⟨hS a⟩
    ∑ r : MarkedPhysicalCanonicalRoot (S a) A B C D,
      ∑ tail : Fin n → ↥(markedPhysicalCanonicalTargets hA hC r Z),
        markedPhysicalPositionPathExtend (fun pos => markedPhysicalPathArrayExtend F pos a)
          (Fin.cons (α := fun _ : Fin (n+1) => ℤ × ℤ) (markedPhysicalCanonicalRootPosition r)
            (fun v => markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r)
              (markedPhysicalCanonicalCompletion r) (tail v).1))

theorem markedPhysicalPath_sum_residue_coordinates {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (Z : Finset (ℤ × ℤ)) (n : ℕ)
    (S : MarkedPhysicalLabelPath P M n → ℕ) (hS : ∀ a,S a≠0)
    {A B C D : ℝ} (hA : 1<A) (hC : 1<C)
    (hbox : Z⊆markedPhysicalPrimitiveBox A B C D)
    (F : (Fin (n+1) → MarkedPhysicalState P M Z) → ℂ) :
    (∑ p,F p)=markedPhysicalPathResidueCoordinatesSum P M Z n S hS (B := B) (D := D) hA hC F := by
  rw [markedPhysicalPathArrayExtend_sum P M Z n F]
  apply Finset.sum_congr rfl
  intro a _
  let : NeZero (S a) := ⟨hS a⟩
  exact markedPhysicalPositionPath_sum_residue_coordinates hA hC Z hbox n
    (fun pos => markedPhysicalPathArrayExtend F pos a)

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime) (V : J → ℝ)
  (pads : ℕ) (Z : Finset (ℤ × ℤ)) (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)

def markedPhysicalMomentPathTerm
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (R : ℕ)
    (p : MarkedPhysicalMomentPath P (pads+1) Z R) : ℂ :=
  if (p 0).1.1=(p (Fin.last (2*R))).1.1 ∧ (∀ v,G (p v)) then
    ∑ copies : Fin (2*R) → (J → Equiv.Perm (Fin (pads+1))) × (J → Equiv.Perm (Fin (pads+1))),
      ∏ v : Fin (2*R),markedPhysicalMomentGeometricCopy P hP V pads Z hZ ψ η d₀ Y Q q
        v.val (p v.castSucc) (p v.succ) (copies v)
  else 0

theorem markedPhysicalPositionMoment_residue_coordinates
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (G : MarkedPhysicalState P (pads+1) Z → Prop) (hV : ∀ j,0≤V j) (R : ℕ) (hR : 0<R)
    (S : MarkedPhysicalLabelPath P (pads+1) (2*R) → ℕ) (hS : ∀ a,S a≠0)
    {A B C D : ℝ} (hA : 1<A) (hC : 1<C) (hbox : Z⊆markedPhysicalPrimitiveBox A B C D) :
    markedPhysicalPositionMoment P (pads+1) Z V
      (markedPhysicalRestrictedMatrix P hP V pads Z hZ ψ η d₀ Y Q q G) R =
      markedPhysicalMass V (pads+1)*
        (markedPhysicalPathResidueCoordinatesSum P (pads+1) Z (2*R) S hS (B := B) (D := D) hA hC
          (markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R)).re := by
  rw [markedPhysicalPositionMoment_geometric_paths P hP V pads Z hZ ψ η d₀ Y Q q hdisj G hV R hR]
  congr 2
  exact markedPhysicalPath_sum_residue_coordinates P (pads+1) Z (2*R) S hS hA hC hbox
    (markedPhysicalMomentPathTerm P hP V pads Z hZ ψ η d₀ Y Q q G R)

end
end ArtinMatthews
