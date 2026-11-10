module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Regularity
public import OAI.Analysis.PDE.Weak.Elliptic.SmoothBounded
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Green.GreenReal


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem smooth_scalar_weak_derivative
    {f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin (m + 1)) :
    HasWeakDirectionalDerivative volume (Pi.single j 1) f (coordinateDerivative f j) := by
  intro φ hφ hs
  simpa only [coordinateDerivative, RCLike.inner_apply, conj_trivial, mul_comm] using
    OAI.Analysis.PDE.Green.integral_directional_by_parts hφ hf hs (Pi.single j 1)

theorem weakRegularity_of_smooth_compact
    {f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)) (k : ℕ) :
    WeakRegularity Ω k ((hf.continuous.memLp_of_hasCompactSupport hs).toLp f) := by
  induction k generalizing f with
  | zero => trivial
  | succ k ih =>
    intro j
    have hd := contDiff_coordinateDerivative hf j
    have hds : HasCompactSupport (coordinateDerivative f j) := hs.fderiv_apply ℝ _
    let g : Lp ℝ 2 (volume : Measure (OAI.Analysis.PDE.Variational.CellCoordinates m)) :=
      (hd.continuous.memLp_of_hasCompactSupport hds).toLp (coordinateDerivative f j)
    refine ⟨g, ?_, ih hd hds⟩
    apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on volume
      (smooth_scalar_weak_derivative (hf.of_le (by simp)) j).on
    · filter_upwards [(hf.continuous.memLp_of_hasCompactSupport hs).coeFn_toLp] with x hx
      exact fun _ ↦ hx.symm
    · filter_upwards [(hd.continuous.memLp_of_hasCompactSupport hds).coeFn_toLp] with x hx
      exact fun _ ↦ hx.symm

end OAI.Analysis.PDE.Weak
