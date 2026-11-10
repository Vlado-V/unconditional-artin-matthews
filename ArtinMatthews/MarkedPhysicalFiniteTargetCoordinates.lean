module

public import ArtinMatthews.MarkedPhysicalRootTargetReindex
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

/-! The actual unimodular target-coordinate map restricted to the finite
original target set. It is a genuine equivalence with its exact image. -/
namespace ArtinMatthews
noncomputable section
open scoped Classical

def markedPhysicalFiniteTargetEquiv {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1<A) (hC : 1<C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) : Z ≃ ↥(markedPhysicalCanonicalTargets hA hC r Z) where
  toFun z := ⟨markedPhysicalCanonicalTargetEquiv hA hC r z.1,
    Finset.mem_image.mpr ⟨z.1,z.2,rfl⟩⟩
  invFun z := ⟨(markedPhysicalCanonicalTargetEquiv hA hC r).symm z.1,
    (markedPhysicalCanonicalTargets_mem hA hC r Z z.1).mp z.2⟩
  left_inv z := by apply Subtype.ext; exact Equiv.symm_apply_apply _ _
  right_inv z := by apply Subtype.ext; exact Equiv.apply_symm_apply _ _

theorem markedPhysicalFiniteTargetEquiv_apply {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1<A) (hC : 1<C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) (z : Z) :
    ((markedPhysicalFiniteTargetEquiv hA hC r Z) z).1=
      markedPhysicalRootCoordinates (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r) z.1 := rfl

theorem markedPhysicalFiniteTargetEquiv_symm_apply {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1<A) (hC : 1<C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) (z : markedPhysicalCanonicalTargets hA hC r Z) :
    ((markedPhysicalFiniteTargetEquiv hA hC r Z).symm z).1=
      markedPhysicalRootLift (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r) z.1 := rfl

theorem markedPhysicalCanonicalTargets_card {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1<A) (hC : 1<C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) : (markedPhysicalCanonicalTargets hA hC r Z).card=Z.card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (markedPhysicalFiniteTargetEquiv hA hC r Z)).symm

end
end ArtinMatthews
