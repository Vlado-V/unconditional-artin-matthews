module

public import ArtinMatthews.SpectralGamma0EllipticCoordinates
public import ArtinMatthews.CuspAverageProjectionOperator
public import ArtinMatthews.SpectralCuspWeightedLocalIntegrability
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

/-! Actual bounded restriction from hyperbolic strip L² to a bounded Euclidean
band, together with the inverse native-coordinate pullback. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace ArtinMatthews

def spectralEllipticBand (w a b : ℝ) : Set (ℝ × ℝ) := Ioc 0 w ×ˢ Icc a b

theorem spectralEllipticBand_measurable (w a b : ℝ) :
    MeasurableSet (spectralEllipticBand w a b) :=
  measurableSet_Ioc.prod measurableSet_Icc

theorem cuspStripMeasure_band_le (w : ℝ) {Y a b : ℝ} (hY : 0 < Y) (ha : Y < a) :
    volume.restrict (spectralEllipticBand w a b) ≤
      ENNReal.ofReal (b^2) • cuspStripMeasure w Y := by
  change (volume.prod volume).restrict (Ioc 0 w ×ˢ Icc a b) ≤ _
  rw [← Measure.prod_restrict]
  calc
    _ ≤ (volume.restrict (Ioc 0 w)).prod
        (ENNReal.ofReal (b^2) • cuspVerticalMeasure Y) :=
      Measure.prod_mono le_rfl (cuspVerticalMeasure_interval_le hY ha)
    _ = _ := by rw [Measure.prod_smul_right]; rfl

def spectralEllipticStripBand (w : ℝ) {Y a b : ℝ} (hY : 0 < Y) (ha : Y < a) :
    CuspStripL2 w Y →L[ℝ] Lp ℂ 2 (volume.restrict (spectralEllipticBand w a b)) :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (cuspStripMeasure_band_le w hY ha)

theorem spectralEllipticStripBand_ae (w : ℝ) {Y a b : ℝ} (hY : 0 < Y) (ha : Y < a)
    (f : CuspStripL2 w Y) :
    spectralEllipticStripBand w (b := b) hY ha f
      =ᵐ[volume.restrict (spectralEllipticBand w a b)] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

theorem spectralEllipticCoordinates_symm_measurePreserving :
    MeasurePreserving (spectralEllipticCoordinates.symm : (ℝ × ℝ) → (Fin 2 → ℝ))
      volume volume :=
  MeasurePreserving.symm spectralEllipticCoordinates.toHomeomorph.toMeasurableEquiv
    spectralEllipticCoordinates_measurePreserving

def spectralEllipticNativeToPlane :
    Lp ℝ 2 (volume : Measure (Fin 2 → ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (ℝ × ℝ)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ spectralEllipticCoordinates.symm
    spectralEllipticCoordinates_symm_measurePreserving).toContinuousLinearMap

theorem spectralEllipticNativeToPlane_ae (f : Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))) :
    spectralEllipticNativeToPlane f =ᵐ[volume] fun p => f (spectralEllipticCoordinates.symm p) :=
  Lp.coeFn_compMeasurePreserving _ _

def spectralEllipticPlaneToBand (w a b : ℝ) :
    Lp ℝ 2 (volume : Measure (ℝ × ℝ)) →L[ℝ]
      Lp ℝ 2 (volume.restrict (spectralEllipticBand w a b)) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using Measure.restrict_le_self)

theorem spectralEllipticPlaneToBand_ae (w a b : ℝ) (f : Lp ℝ 2 (volume : Measure (ℝ × ℝ))) :
    spectralEllipticPlaneToBand w a b f
      =ᵐ[volume.restrict (spectralEllipticBand w a b)] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

end ArtinMatthews
