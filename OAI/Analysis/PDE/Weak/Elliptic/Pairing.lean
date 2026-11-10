module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Variational.CellL2
public import OAI.Analysis.PDE.Weak.CalculusWeakDifference
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Weak.Elliptic.Difference


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem integral_differenceQuotient_inner (μ : Measure X) [μ.IsAddRightInvariant]
    (v : X) (h : ℝ) (U Φ : X → V)
    (hzero : Integrable (fun x ↦ inner ℝ (U x) (Φ x)) μ)
    (hshift : Integrable (fun x ↦ inner ℝ (U (x + h • v)) (Φ x)) μ) :
    (∫ x, inner ℝ (differenceQuotient v h U x) (Φ x) ∂μ) =
      -(∫ x, inner ℝ (U x) (differenceQuotient v (-h) Φ x) ∂μ) := by
  have hback : Integrable (fun x ↦ inner ℝ (U x) (Φ (x - h • v))) μ := by
    have ht := hshift.comp_add_right (-(h • v))
    simpa only [neg_add_cancel_right, sub_eq_add_neg] using ht
  have htrans : (∫ x, inner ℝ (U (x + h • v)) (Φ x) ∂μ) =
      ∫ x, inner ℝ (U x) (Φ (x - h • v)) ∂μ := by
    simpa only [add_sub_cancel_right] using
      (integral_add_right_eq_self (fun x ↦ inner ℝ (U x) (Φ (x - h • v)))
        (h • v) (μ := μ))
  have heq : (fun x ↦ inner ℝ (U x) (differenceQuotient v (-h) Φ x)) =
      fun x ↦ -(h⁻¹) * (inner ℝ (U x) (Φ (x - h • v)) - inner ℝ (U x) (Φ x)) := by
    funext x
    simp only [differenceQuotient, inv_neg, neg_smul, real_inner_smul_right,
      sub_eq_add_neg, inner_neg_right, inner_add_right]
    ring
  simp only [differenceQuotient, real_inner_smul_left, inner_sub_left]
  rw [integral_const_mul, integral_sub hshift hzero, htrans]
  change _ = -(∫ x, inner ℝ (U x) (differenceQuotient v (-h) Φ x) ∂μ)
  rw [heq, integral_const_mul, integral_sub hback hzero]
  ring

open OAI.Analysis.PDE.Variational
variable {m : ℕ}

theorem cellGradient_differenceQuotient (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ)
    {u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hu : Differentiable ℝ u) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Variational.cellGradient (differenceQuotient v h u) x =
      differenceQuotient v h (OAI.Analysis.PDE.Variational.cellGradient u) x := by
  ext i
  exact fderiv_differenceQuotient v h hu x (Pi.single i 1)

theorem cellGradient_cutoff_square {η u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hη : Differentiable ℝ η) (hu : Differentiable ℝ u) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Variational.cellGradient (fun y ↦ η y ^ 2 * u y) x =
      η x ^ 2 • OAI.Analysis.PDE.Variational.cellGradient u x + (2 * η x * u x) • OAI.Analysis.PDE.Variational.cellGradient η x := by
  ext i
  change fderiv ℝ ((fun y ↦ η y ^ 2) * u) x (Pi.single i 1) = _
  rw [(((hη x).hasFDerivAt.pow 2).mul (hu x).hasFDerivAt).fderiv]
  simp
  ring

/-- The exact translated weak equation against an actual differentiable
test. It is the starting point of the interior difference-quotient estimate. -/
theorem shifted_weak_equation (v : OAI.Analysis.PDE.Variational.CellCoordinates m) (h : ℝ)
    (H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) (f w : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (hw : Differentiable ℝ w)
    (hzero : Integrable (fun x ↦ inner ℝ (H x) (OAI.Analysis.PDE.Variational.cellGradient w x)))
    (hshift : Integrable (fun x ↦ inner ℝ (H (x + h • v)) (OAI.Analysis.PDE.Variational.cellGradient w x)))
    (hweak : (∫ x, inner ℝ (H x) (OAI.Analysis.PDE.Variational.cellGradient (differenceQuotient v (-h) w) x)) =
      ∫ x, f x * differenceQuotient v (-h) w x) :
    (∫ x, inner ℝ (differenceQuotient v h H x) (OAI.Analysis.PDE.Variational.cellGradient w x)) =
      -(∫ x, f x * differenceQuotient v (-h) w x) := by
  rw [integral_differenceQuotient_inner volume v h H (OAI.Analysis.PDE.Variational.cellGradient w) hzero hshift]
  simp_rw [← cellGradient_differenceQuotient v (-h) hw]
  rw [hweak]

end OAI.Analysis.PDE.Weak
