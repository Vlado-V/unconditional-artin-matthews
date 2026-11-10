module

public import ArtinMatthews.SpectralSectionWeakPairing
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact coordinates and real scalar projections for applying the native
Euclidean H1Pair interior regularity theorem in two dimensions. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace ArtinMatthews

def spectralEllipticCoordinates : (Fin 2 → ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.finTwoArrow ℝ ℝ

theorem spectralEllipticCoordinates_apply (x : Fin 2 → ℝ) :
    spectralEllipticCoordinates x = (x 0,x 1) := rfl

theorem spectralEllipticCoordinates_measurePreserving :
    MeasurePreserving (spectralEllipticCoordinates : (Fin 2 → ℝ) → ℝ × ℝ) volume volume :=
  volume_preserving_finTwoArrow ℝ

theorem spectralEllipticCoordinates_integral (F : ℝ × ℝ → ℝ) :
    (∫ x : Fin 2 → ℝ, F (spectralEllipticCoordinates x)) = ∫ p, F p :=
  (volume_preserving_finTwoArrow ℝ).integral_comp' F

theorem spectralEllipticCoordinates_single (i : Fin 2) :
    spectralEllipticCoordinates (Pi.single i 1) = spectralPlaneDirection i := by
  fin_cases i <;> simp [spectralEllipticCoordinates_apply,spectralPlaneDirection]

def spectralEllipticScalar (L : ℂ →L[ℝ] ℝ) (F : ℝ × ℝ → ℂ) (x : Fin 2 → ℝ) : ℝ :=
  L (F (spectralEllipticCoordinates x))

theorem spectralEllipticScalar_contDiff (L : ℂ →L[ℝ] ℝ) (F : ℝ × ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (spectralEllipticScalar L F) :=
  L.contDiff.comp (hF.comp spectralEllipticCoordinates.contDiff)

theorem spectralEllipticScalar_compact (L : ℂ →L[ℝ] ℝ) (F : ℝ × ℝ → ℂ)
    (hc : HasCompactSupport F) : HasCompactSupport (spectralEllipticScalar L F) :=
  (hc.comp_homeomorph spectralEllipticCoordinates.toHomeomorph).comp_left L.map_zero

theorem spectralEllipticScalar_derivative (L : ℂ →L[ℝ] ℝ) (F : ℝ × ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (x : Fin 2 → ℝ) (i : Fin 2) :
    fderiv ℝ (spectralEllipticScalar L F) x (Pi.single i 1) =
      L (fderiv ℝ F (spectralEllipticCoordinates x) (spectralPlaneDirection i)) := by
  have hd := L.hasFDerivAt.comp x
    (((hF.differentiable (by simp) (spectralEllipticCoordinates x)).hasFDerivAt).comp x
      spectralEllipticCoordinates.hasFDerivAt)
  change fderiv ℝ (L ∘ F ∘ spectralEllipticCoordinates) x (Pi.single i 1) = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    spectralEllipticCoordinates_single]

theorem spectralEllipticScalar_sq_le (L : ℂ →L[ℝ] ℝ) (F : ℝ × ℝ → ℂ)
    (x : Fin 2 → ℝ) :
    ‖spectralEllipticScalar L F x‖^2 ≤ ‖L‖^2 * ‖F (spectralEllipticCoordinates x)‖^2 := by
  simpa only [spectralEllipticScalar,mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (L.le_opNorm (F (spectralEllipticCoordinates x))) 2

theorem spectralEllipticScalar_derivative_sq_le (L : ℂ →L[ℝ] ℝ) (F : ℝ × ℝ → ℂ)
    (hF : ContDiff ℝ ∞ F) (x : Fin 2 → ℝ) :
    (∑ i : Fin 2, ‖fderiv ℝ (spectralEllipticScalar L F) x (Pi.single i 1)‖^2) ≤
      ‖L‖^2 * ∑ i : Fin 2,
        ‖fderiv ℝ F (spectralEllipticCoordinates x) (spectralPlaneDirection i)‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [spectralEllipticScalar_derivative L F hF]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (L.le_opNorm (fderiv ℝ F (spectralEllipticCoordinates x) (spectralPlaneDirection i))) 2

end ArtinMatthews
