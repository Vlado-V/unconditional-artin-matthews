module

public import ArtinMatthews.MarkedRawGoodArcAgreement
public import ArtinMatthews.MarkedTypeIITransport
public import ArtinMatthews.MarkedPhysicalRootCoordinates
public import ArtinMatthews.MarkedPhysicalCompletionGood
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


set_option backward.privateInPublic true
@[expose] public section

/-! At every integer root, the original physical good test is exactly
the fixed-coordinate Möbius test used by the continuous path observable. -/

noncomputable section
namespace ArtinMatthews

def markedRootIntegerVector (z : ℤ × ℤ) : Fin 2 → ℝ := ![(z.1:ℝ),(z.2:ℝ)]

theorem markedPhysicalRootLift_det (root completion z w : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion=1) :
    markedMinorIntegerDet (markedPhysicalRootLift root completion z) (markedPhysicalRootLift root completion w) =
      markedMinorIntegerDet z w := by
  calc
    _ = markedMinorIntegerDet root completion*markedMinorIntegerDet z w := by
      unfold markedPhysicalRootLift markedMinorIntegerDet
      ring
    _ = _ := by rw [hdet,one_mul]

theorem markedPhysicalRootLift_first_ratio (root completion z w : ℤ × ℤ)
    (hroot : root.1 ≠ 0) :
    ((markedPhysicalRootLift root completion w).1:ℝ)/((markedPhysicalRootLift root completion z).1:ℝ) =
      markedTransportedRatio ((completion.1:ℝ)/root.1) (markedRootIntegerVector z) (markedRootIntegerVector w) := by
  have hr : (root.1:ℝ) ≠ 0 := by exact_mod_cast hroot
  have hf (v : ℤ × ℤ) : ((markedPhysicalRootLift root completion v).1:ℝ) =
      (root.1:ℝ)*markedTau ((completion.1:ℝ)/root.1) (markedRootIntegerVector v) := by
    simp only [markedPhysicalRootLift,Int.cast_add,Int.cast_mul,markedTau,markedRootIntegerVector,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    field_simp
  rw [hf w,hf z,mul_div_mul_left _ _ hr]
  rfl

theorem markedRawDirtyGood_root_lift {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (actualCompletion : Z → ℤ × ℤ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z)
    (root completion z w : ℤ × ℤ)
    (hroot : root.1 ≠ 0) (hdet : markedMinorIntegerDet root completion=1)
    (hzw : markedMinorIntegerDet z w=1) (hpos : s.1.1=markedPhysicalRootLift root completion z)
    (hactual : markedMinorIntegerDet s.1.1 (actualCompletion s.1)=1) :
    MarkedRawDirtyGood e x 0 d₀ Y actualCompletion s ↔
      MarkedRawCircleGood e x s.2.1 d₀ Y
        (markedTransportedRatio ((completion.1:ℝ)/root.1) (markedRootIntegerVector z)
          (markedRootIntegerVector w):AddCircle (1:ℝ)) := by
  rw [markedRawDirtyGood_iff_circle]
  simp only [markedMinorIntegerTau,zero_mul,add_zero]
  have hc : markedMinorIntegerDet s.1.1 (markedPhysicalRootLift root completion w)=1 := by
    rw [hpos,markedPhysicalRootLift_det root completion z w hdet,hzw]
  rw [markedPhysical_completion_ratio_circle s.1.1 (markedPhysicalRootLift root completion w)
    (actualCompletion s.1) hc hactual,hpos,markedPhysicalRootLift_first_ratio root completion z w hroot]

end ArtinMatthews
