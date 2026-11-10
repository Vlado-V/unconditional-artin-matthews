module

public import ArtinMatthews.MarkedMinorArcDirtyGoodCutoff
public import ArtinMatthews.MarkedRawGoodRootMeasure
public import ArtinMatthews.MarkedPhysicalRootCoordinates
public import ArtinMatthews.MarkedRawGoodRootBridge
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The physical good test is independent of the determinant-one
completion at the source root. Thus its original complement can be
replaced by the canonical completion used for integer-root counting. -/

noncomputable section
namespace ArtinMatthews

theorem markedPhysical_completion_first_shift (root completion other : ℤ × ℤ)
    (hc : markedMinorIntegerDet root completion = 1)
    (ho : markedMinorIntegerDet root other = 1) :
    other.1 = completion.1 + markedMinorIntegerDet other completion * root.1 := by
  have h := congrArg Prod.fst (markedPhysicalRootLift_coordinates root completion other hc)
  change markedMinorIntegerDet other completion * root.1 +
    markedMinorIntegerDet root other * completion.1 = other.1 at h
  rw [ho, one_mul] at h
  linarith

theorem markedPhysical_completion_ratio_circle (root completion other : ℤ × ℤ)
    (hc : markedMinorIntegerDet root completion = 1)
    (ho : markedMinorIntegerDet root other = 1) :
    (((other.1 : ℝ)/(root.1 : ℝ)) : AddCircle (1 : ℝ)) =
      (((completion.1 : ℝ)/(root.1 : ℝ)) : AddCircle (1 : ℝ)) := by
  by_cases hr : root.1 = 0
  · simp only [hr, Int.cast_zero, div_zero]
  have hrR : (root.1 : ℝ) ≠ 0 := by exact_mod_cast hr
  have hs : (other.1 : ℝ) = (completion.1 : ℝ) +
      (markedMinorIntegerDet other completion : ℝ) * (root.1 : ℝ) := by
    exact_mod_cast markedPhysical_completion_first_shift root completion other hc ho
  have hratio : (other.1 : ℝ)/(root.1 : ℝ) =
      (completion.1 : ℝ)/(root.1 : ℝ) + (markedMinorIntegerDet other completion : ℝ) := by
    apply (div_eq_iff hrR).mpr
    calc
      _ = (completion.1 : ℝ) + (markedMinorIntegerDet other completion : ℝ) * (root.1 : ℝ) := hs
      _ = _ := by field_simp
  rw [hratio, AddCircle.coe_add]
  have hz : (((markedMinorIntegerDet other completion : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨markedMinorIntegerDet other completion, by simp⟩
  rw [hz, add_zero]

theorem markedRawDirtyGood_zero_canonical_completion
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x d₀ Y : ℝ) {B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ)
    (s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x) B Z)
    (completion : ℤ × ℤ)
    (hw : markedMinorIntegerDet s.1.1 (w s.1) = 1)
    (hc : markedMinorIntegerDet s.1.1 completion = 1) :
    MarkedRawDirtyGood e x 0 d₀ Y w s ↔
      (((completion.1 : ℝ)/(s.1.1.1 : ℝ)) : AddCircle (1 : ℝ)) ∉
        markedRawBadRootSet e x d₀ Y s.2.1 := by
  rw [markedRawDirtyGood_iff_not_badRootSet]
  simp only [markedMinorIntegerTau, zero_mul, add_zero]
  rw [markedPhysical_completion_ratio_circle s.1.1 completion (w s.1) hc hw]

end ArtinMatthews
