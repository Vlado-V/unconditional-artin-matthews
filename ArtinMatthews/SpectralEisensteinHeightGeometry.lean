module

public import ArtinMatthews.SpectralEisensteinLogGeometry
public import Mathlib.Analysis.InnerProductSpace.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact real first and second derivatives of the normalized row height.
These identities support arbitrary actual smooth radial profiles. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ArtinMatthews

def eisensteinNormalizedRowHeight (w c d : ℝ) (p : ℝ×ℝ) : ℝ :=
  Real.exp (eisensteinRowLog c d p)/w

def eisensteinNormalizedRowHeightX (w c d : ℝ) (p : ℝ×ℝ) : ℝ :=
  eisensteinNormalizedRowHeight w c d p*eisensteinRowLogX c d p

def eisensteinNormalizedRowHeightY (w c d : ℝ) (p : ℝ×ℝ) : ℝ :=
  eisensteinNormalizedRowHeight w c d p*eisensteinRowLogY c d p

def eisensteinNormalizedRowHeightXX (w c d : ℝ) (p : ℝ×ℝ) : ℝ :=
  eisensteinNormalizedRowHeight w c d p*((eisensteinRowLogX c d p)^2+eisensteinRowLogXX c d p)

def eisensteinNormalizedRowHeightXY (w c d : ℝ) (p : ℝ×ℝ) : ℝ :=
  eisensteinNormalizedRowHeight w c d p*(eisensteinRowLogX c d p*eisensteinRowLogY c d p+
    eisensteinRowLogXY c d p)

def eisensteinNormalizedRowHeightYY (w c d : ℝ) (p : ℝ×ℝ) : ℝ :=
  eisensteinNormalizedRowHeight w c d p*((eisensteinRowLogY c d p)^2+eisensteinRowLogYY c d p)

theorem eisensteinNormalizedRowHeight_eq (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    eisensteinNormalizedRowHeight w c d p=p.2/(w*eisensteinRowQuadratic c d p) := by
  unfold eisensteinNormalizedRowHeight eisensteinRowLog
  rw [Real.exp_sub,Real.exp_log hp,Real.exp_log (eisensteinRowQuadratic_pos c d hcd p hp)]
  rw [div_div,mul_comm w]

theorem eisensteinNormalizedRowHeight_hasFDerivAt (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinNormalizedRowHeight w c d)
      (spectralPlaneDerivative (eisensteinNormalizedRowHeightX w c d p)
        (eisensteinNormalizedRowHeightY w c d p)) p := by
  have h := ((eisensteinRowLog_hasFDerivAt c d hcd p hp).exp).mul_const w⁻¹
  change HasFDerivAt (fun q => Real.exp (eisensteinRowLog c d q)*w⁻¹) _ p
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [eisensteinNormalizedRowHeight,eisensteinNormalizedRowHeightX,eisensteinNormalizedRowHeightY,
    spectralPlaneDerivative]
  ring

theorem eisensteinNormalizedRowHeightX_hasFDerivAt (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinNormalizedRowHeightX w c d)
      (spectralPlaneDerivative (eisensteinNormalizedRowHeightXX w c d p)
        (eisensteinNormalizedRowHeightXY w c d p)) p := by
  have h := (eisensteinNormalizedRowHeight_hasFDerivAt w c d hcd p hp).mul
    (eisensteinRowLogX_hasFDerivAt c d hcd p hp)
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [eisensteinNormalizedRowHeightX,eisensteinNormalizedRowHeightY,
    eisensteinNormalizedRowHeightXX,eisensteinNormalizedRowHeightXY,spectralPlaneDerivative]
  ring

theorem eisensteinNormalizedRowHeightY_hasFDerivAt (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinNormalizedRowHeightY w c d)
      (spectralPlaneDerivative (eisensteinNormalizedRowHeightXY w c d p)
        (eisensteinNormalizedRowHeightYY w c d p)) p := by
  have h := (eisensteinNormalizedRowHeight_hasFDerivAt w c d hcd p hp).mul
    (eisensteinRowLogY_hasFDerivAt c d hcd p hp)
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [eisensteinNormalizedRowHeightX,eisensteinNormalizedRowHeightY,
    eisensteinNormalizedRowHeightXY,eisensteinNormalizedRowHeightYY,spectralPlaneDerivative]
  ring

theorem eisensteinNormalizedRowHeight_trace_zero (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    eisensteinNormalizedRowHeightXX w c d p+eisensteinNormalizedRowHeightYY w c d p=0 := by
  have he := eisensteinRowLog_eikonal c d hcd p hp
  have hl := eisensteinRowLog_laplacian c d hcd p hp
  unfold eisensteinNormalizedRowHeightXX eisensteinNormalizedRowHeightYY
  calc
    _=eisensteinNormalizedRowHeight w c d p*
      ((eisensteinRowLogX c d p)^2+(eisensteinRowLogY c d p)^2+
        (eisensteinRowLogXX c d p+eisensteinRowLogYY c d p)) := by ring
    _=0 := by rw [he,hl];ring

theorem eisensteinNormalizedRowHeight_grad_sq (w c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ×ℝ) (hp : 0 < p.2) :
    (eisensteinNormalizedRowHeightX w c d p)^2+(eisensteinNormalizedRowHeightY w c d p)^2=
      (eisensteinNormalizedRowHeight w c d p)^2/p.2^2 := by
  unfold eisensteinNormalizedRowHeightX eisensteinNormalizedRowHeightY
  calc
    _=(eisensteinNormalizedRowHeight w c d p)^2*
      ((eisensteinRowLogX c d p)^2+(eisensteinRowLogY c d p)^2) := by ring
    _=_ := by rw [eisensteinRowLog_eikonal c d hcd p hp];ring

end ArtinMatthews
