module

public import ArtinMatthews.MarkedRawGoodRootTransport
public import ArtinMatthews.MarkedPhysicalRootTargetReindex
public import ArtinMatthews.MarkedRootPartitionBox
public import ArtinMatthews.MarkedRootPartitionRoots
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact normalized coordinates of a physical integer lift. The
moving box used in root replacement is the literal primitive physical
box, including its reciprocal determinant-one correction. -/

noncomputable section
namespace ArtinMatthews

def markedPhysicalNormalizedRootPoint (root completion : ℤ × ℤ) (U V : ℝ) : ℝ × (ℝ × ℝ) :=
  ((completion.1:ℝ)/root.1,(root.1:ℝ)/U,(root.2:ℝ)/V)

theorem markedPhysicalLift_root_box_first (root completion z : ℤ × ℤ)
    {U V : ℝ} (hroot : root.1≠0) (hU : U≠0) :
    markedRootBoxFirst (markedRootIntegerVector z) (markedPhysicalNormalizedRootPoint root completion U V) =
      ((markedPhysicalRootLift root completion z).1:ℝ)/U := by
  have hu : (root.1:ℝ)≠0 := by exact_mod_cast hroot
  unfold markedRootBoxFirst markedPhysicalNormalizedRootPoint markedTau markedRootIntegerVector markedPhysicalRootLift
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_add,Int.cast_mul]
  field_simp

theorem markedPhysicalLift_root_box_second (root completion z : ℤ × ℤ)
    {U V : ℝ} (hroot : root.1≠0) (hU : U≠0) (hV : V≠0)
    (hdet : markedMinorIntegerDet root completion=1) :
    markedRootBoxSecond U V (markedRootIntegerVector z) (markedPhysicalNormalizedRootPoint root completion U V) =
      ((markedPhysicalRootLift root completion z).2:ℝ)/V := by
  have hu : (root.1:ℝ)≠0 := by exact_mod_cast hroot
  have hd : (root.1:ℝ)*completion.2-(root.2:ℝ)*completion.1=1 := by
    exact_mod_cast hdet
  unfold markedRootBoxSecond markedPhysicalNormalizedRootPoint markedTau markedRootIntegerVector markedPhysicalRootLift
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_add,Int.cast_mul]
  field_simp
  linear_combination -(z.2:ℝ)*hd

theorem markedPhysicalLift_mem_box_iff (root completion z : ℤ × ℤ)
    {U V : ℝ} (hroot : root.1≠0) (hU : 0<U) (hV : 0<V)
    (hdet : markedMinorIntegerDet root completion=1) (hz : IsCoprime z.1 z.2) :
    markedPhysicalRootLift root completion z ∈ markedPhysicalPrimitiveBox U (16*U) V (2*V) ↔
      MarkedRootPhysicalBox U V (markedRootIntegerVector z)
        (markedPhysicalNormalizedRootPoint root completion U V) := by
  have hp := (markedPhysicalRootLift_primitive_iff root completion z hdet).mpr hz
  rw [MarkedRootPhysicalBox,markedPhysicalLift_root_box_first root completion z hroot hU.ne',
    markedPhysicalLift_root_box_second root completion z hroot hU.ne' hV.ne' hdet]
  simp only [markedPhysicalPrimitiveBox,Finset.mem_filter,hp,and_true]
  constructor
  · intro h
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp h
    have h₁' := (fixedURoot_mem_closed_interval U (16*U) _).mp h₁
    have h₂' := (fixedURoot_mem_closed_interval V (2*V) _).mp h₂
    exact ⟨⟨(le_div_iff₀ hU).mpr (by simpa only [one_mul] using h₁'.1),
      (div_le_iff₀ hU).mpr h₁'.2⟩,
      ⟨(le_div_iff₀ hV).mpr (by simpa only [one_mul] using h₂'.1),
      (div_le_iff₀ hV).mpr h₂'.2⟩⟩
  · rintro ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩
    apply Finset.mem_product.mpr
    exact ⟨(fixedURoot_mem_closed_interval U (16*U) _).mpr
      ⟨by simpa only [one_mul] using (le_div_iff₀ hU).mp h₁,(div_le_iff₀ hU).mp h₂⟩,
      (fixedURoot_mem_closed_interval V (2*V) _).mpr
      ⟨by simpa only [one_mul] using (le_div_iff₀ hV).mp h₃,(div_le_iff₀ hV).mp h₄⟩⟩

theorem markedPhysicalCanonicalRoot_normalized {S : ℕ} {U V : ℝ}
    (r : MarkedPhysicalCanonicalRoot S U (16*U) V (2*V)) :
    markedRootNormalizedPoint U V r.2.1 =
      markedPhysicalNormalizedRootPoint (markedPhysicalCanonicalRootPosition r)
        (markedPhysicalCanonicalCompletion r) U V := rfl

end ArtinMatthews
