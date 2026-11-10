module

public import ArtinMatthews.SpectralRellichCoordinates
import ArtinMatthews.SpectralCoreLocalizationCoordinates
public import ArtinMatthews.CuspAverageProjectionBase
public import ArtinMatthews.SpectralCuspMass
public import ArtinMatthews.SpectralCuspProjectedTail
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Genuine integrability of the smooth cusp value/derivative graph. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set Filter
open scoped ContDiff

def spectralCuspEuclideanMeasure (w Y : ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc 0 w)).prod (volume.restrict (Ioi Y))

theorem spectral_upperHalfPlane_integrableOn_coordinates (G : ℝ × ℝ → ℝ)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    IntegrableOn (fun z : UpperHalfPlane => G (z.re,z.im)) {z | (z.re,z.im) ∈ S} ↔
      IntegrableOn (fun p => G p / p.2^2) S :=
  upperHalfPlane_integrableOn_coordinates G hS hpositive

theorem spectralPlanePartialX_continuous {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) :
    Continuous (spectralPlanePartialX F) := by
  have he : spectralPlanePartialX F = fun p => fderiv ℝ F p (1,0) := by
    funext p
    exact spectralPlanePartialX_eq_fderiv (hF.differentiable (by simp) p)
  rw [he]
  exact (hF.continuous_fderiv (by simp)).clm_apply continuous_const

theorem spectral_cusp_derivative_sq_integrable {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {w Y : ℝ} (hw : 0 < w)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    Integrable (fun p => ‖spectralPlanePartialX F p‖^2) (spectralCuspEuclideanMeasure w Y) := by
  have hd := spectralPlanePartialX_continuous hF
  have hm : AEStronglyMeasurable (fun p => ‖spectralPlanePartialX F p‖^2)
      (spectralCuspEuclideanMeasure w Y) := (hd.norm.pow 2).aestronglyMeasurable
  apply (integrable_prod_iff' hm).mpr
  constructor
  · apply Eventually.of_forall
    intro y
    exact (((hd.comp (continuous_id.prodMk continuous_const)).norm.pow 2).integrableOn_Icc
      (μ := volume) (a := 0) (b := w)).mono_set Ioc_subset_Icc_self
  · have he : (fun y => ∫ x in Ioc 0 w, ‖‖spectralPlanePartialX F (x,y)‖^2‖) =
        cuspHorizontalEnergy F w := by
      funext y
      simp only [Real.norm_of_nonneg (sq_nonneg _), cuspHorizontalEnergy,
        intervalIntegral.integral_of_le hw.le, spectralPlanePartialX]
    rw [he]
    exact henergy

theorem spectral_cusp_mass_density_integrable {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {w Y : ℝ} (hw : 0 < w)
    (hfinite : IntegrableOn (fun y => cuspHorizontalMass F w y / y^2) (Ioi Y)) :
    Integrable (fun p => ‖F p‖^2 / p.2^2) (spectralCuspEuclideanMeasure w Y) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖F p‖^2 / p.2^2)
      (spectralCuspEuclideanMeasure w Y) :=
    ((hF.norm.pow 2).measurable.div (measurable_snd.pow_const 2)).aestronglyMeasurable
  apply (integrable_prod_iff' hm).mpr
  constructor
  · apply Eventually.of_forall
    intro y
    exact (((hF.comp (continuous_id.prodMk continuous_const)).norm.pow 2).integrableOn_Icc
      (μ := volume) (a := 0) (b := w) |>.mono_set Ioc_subset_Icc_self).div_const (y^2)
  · have he : (fun y => ∫ x in Ioc 0 w, ‖‖F (x,y)‖^2 / y^2‖) =
        (fun y => cuspHorizontalMass F w y / y^2) := by
      funext y
      simp only [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)),
        integral_div, cuspHorizontalMass, intervalIntegral.integral_of_le hw.le]
    rw [he]
    exact hfinite

theorem spectral_cusp_projected_memLp {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    MemLp (fun z : UpperHalfPlane => cuspMeanZeroRepresentative w F (z.re,z.im)) 2
      (volume.restrict (hyperbolicCuspStrip w Y)) := by
  have hc := cuspMeanZeroRepresentative_continuous hF.continuous w
  have hs (y : ℝ) (_ : y ∈ Ioi Y) : ContDiff ℝ ∞ (fun x => F (x,y)) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have he : IntegrableOn (cuspHorizontalEnergy (cuspMeanZeroRepresentative w F) w) (Ioi Y) := by
    rwa [cuspMeanZeroRepresentative_energy]
  have hfinite := (cusp_horizontal_tail_bound hc hw hY
    (fun y hy => cuspMeanZeroRepresentative_slice_smooth (hs y hy))
    (fun y _ => cuspMeanZeroRepresentative_mean_zero hF.continuous hw y) he).1
  have hi := spectral_cusp_mass_density_integrable hc hw hfinite
  have hi' : IntegrableOn
      (fun p => ‖cuspMeanZeroRepresentative w F p‖^2 / p.2^2) ((Ioc 0 w) ×ˢ (Ioi Y)) := by
    change Integrable _ ((volume.prod volume).restrict ((Ioc 0 w) ×ˢ (Ioi Y)))
    rw [← Measure.prod_restrict]
    exact hi
  have hh := (spectral_upperHalfPlane_integrableOn_coordinates
    (fun p => ‖cuspMeanZeroRepresentative w F p‖^2)
    (measurableSet_Ioc.prod measurableSet_Ioi) (fun p hp => hY.trans hp.2)).mpr hi'
  exact (memLp_two_iff_integrable_sq_norm
    ((hc.comp (by fun_prop : Continuous (fun z : UpperHalfPlane => (z.re,z.im)))).aestronglyMeasurable)).mpr hh

theorem spectral_cusp_derivative_memLp {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {w Y : ℝ} (hw : 0 < w)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    MemLp (spectralPlanePartialX F) 2 (spectralCuspEuclideanMeasure w Y) :=
  (memLp_two_iff_integrable_sq_norm (spectralPlanePartialX_continuous hF).aestronglyMeasurable).mpr
    (spectral_cusp_derivative_sq_integrable hF hw henergy)

end ArtinMatthews
