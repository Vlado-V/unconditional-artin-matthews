module

public import ArtinMatthews.MarkedPhysicalCanonicalRoots
public import ArtinMatthews.MarkedPhysicalRootResidue
public import ArtinMatthews.FixedURootReciprocalBoxes
public import ArtinMatthews.FixedURootWeightedGeometry
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

/-! The canonical completion gives an exact integer change of coordinates
for the target sum, with no loss of primitivity or target support. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedPhysicalCanonicalCompletion {S : ℕ} {A B C D : ℝ}
    (r : MarkedPhysicalCanonicalRoot S A B C D) : ℤ × ℤ :=
  ((r.2.1).2.1,(1+(r.2.1).2.2*(r.2.1).2.1)/(r.2.1).1)

theorem markedPhysicalCanonicalCompletion_det {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C) (r : MarkedPhysicalCanonicalRoot S A B C D) :
    markedMinorIntegerDet (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r)=1 := by
  obtain ⟨d,hu,_,_,_,_,_,hd,_⟩ :=
    fixedURootReciprocal_box_canonical hA hC (by norm_num) (by norm_num) r.2.2
  have hune : (r.2.1).1 ≠ 0 := (zero_lt_one.trans hu).ne'
  unfold markedPhysicalCanonicalCompletion markedPhysicalCanonicalRootPosition fixedURootFirstColumn
  rw [fixedURootReciprocal_completion_eq hune hd]
  exact hd

theorem markedPhysicalCanonicalCompletion_reduction {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C) (r : MarkedPhysicalCanonicalRoot S A B C D) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S))
      (markedPhysicalRootMatrix (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r)
        (markedPhysicalCanonicalCompletion_det hA hC r)) = r.1 := by
  obtain ⟨d,hd,hred⟩ := fixedURootMatrixBox_integer_root r.1 A B 0 1 C D true true hA hC
    (by norm_num) (by norm_num) r.2.1 r.2.2
  have hu := (fixedURootMatrixBox_coordinate_bounds r.1 A B 0 1 C D true true r.2.1 r.2.2).1.1
  have hune : (r.2.1).1 ≠ 0 := by
    intro hz
    simp only [hz,Int.cast_zero] at hu
    linarith
  have he : markedPhysicalCanonicalCompletion r=((r.2.1).2.1,d) := by
    unfold markedPhysicalCanonicalCompletion
    rw [fixedURootReciprocal_completion_eq hune hd]
  simpa only [he,markedPhysicalCanonicalRootPosition,fixedURootFirstColumn] using hred

def markedPhysicalCanonicalTargetEquiv {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C) (r : MarkedPhysicalCanonicalRoot S A B C D) :
    (ℤ × ℤ) ≃ (ℤ × ℤ) :=
  markedPhysicalRootEquiv (markedPhysicalCanonicalRootPosition r) (markedPhysicalCanonicalCompletion r)
    (markedPhysicalCanonicalCompletion_det hA hC r)

def markedPhysicalCanonicalTargets {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  Z.image (markedPhysicalCanonicalTargetEquiv hA hC r)

theorem markedPhysicalCanonicalTargets_mem {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) (z : ℤ × ℤ) :
    z ∈ markedPhysicalCanonicalTargets hA hC r Z ↔
      (markedPhysicalCanonicalTargetEquiv hA hC r).symm z ∈ Z := by
  constructor
  · rintro hz
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hz
    rw [← he,Equiv.symm_apply_apply]
    exact hw
  · intro hz
    exact Finset.mem_image.mpr ⟨_,hz,Equiv.apply_symm_apply _ z⟩

theorem markedPhysicalCanonicalTargets_sum {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) (F : (ℤ × ℤ) → ℂ) :
    (∑ w ∈ Z,F w) = ∑ z ∈ markedPhysicalCanonicalTargets hA hC r Z,
      F ((markedPhysicalCanonicalTargetEquiv hA hC r).symm z) := by
  unfold markedPhysicalCanonicalTargets
  rw [Finset.sum_image]
  · simp only [Equiv.symm_apply_apply]
  · exact fun _ _ _ _ h => (markedPhysicalCanonicalTargetEquiv hA hC r).injective h

theorem markedPhysicalCanonicalTargets_primitive {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C) (r : MarkedPhysicalCanonicalRoot S A B C D)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (z : ℤ × ℤ) (hz : z ∈ markedPhysicalCanonicalTargets hA hC r Z) : IsCoprime z.1 z.2 := by
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
  exact (markedPhysicalRootCoordinates_primitive_iff _ _ _ (markedPhysicalCanonicalCompletion_det hA hC r)).mpr (hZ w hw)

end ArtinMatthews
