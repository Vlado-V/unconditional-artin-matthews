module

public import ArtinMatthews.SpectralCuspGraphIntegrability
public import ArtinMatthews.SpectralCuspProjectedTail
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
public import Mathlib.MeasureTheory.Function.L2Space
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

/-! The actual smooth value/derivative graph and its cusp-tail bound under closure. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set
open scoped ContDiff

noncomputable def spectralCuspProjectedLp {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y)) :=
  (spectral_cusp_projected_memLp hF hw hY henergy).toLp
    (fun z : UpperHalfPlane => cuspMeanZeroRepresentative w F (z.re,z.im))

noncomputable def spectralCuspDerivativeLp {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {w Y : ℝ} (hw : 0 < w)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    Lp ℂ 2 (spectralCuspEuclideanMeasure w Y) :=
  (spectral_cusp_derivative_memLp hF hw henergy).toLp (spectralPlanePartialX F)

theorem spectralCuspProjectedLp_ae {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    spectralCuspProjectedLp hF hw hY henergy =ᵐ[volume.restrict (hyperbolicCuspStrip w Y)]
      (fun z : UpperHalfPlane => cuspMeanZeroRepresentative w F (z.re,z.im)) :=
  MemLp.coeFn_toLp _

/-- The derivative component of the generating graph is the literal horizontal
derivative of the mean-zero value component, almost everywhere. -/
theorem spectralCuspDerivativeLp_ae {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {w Y : ℝ} (hw : 0 < w)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    spectralCuspDerivativeLp hF hw henergy =ᵐ[spectralCuspEuclideanMeasure w Y]
      (fun p => deriv (fun t => cuspMeanZeroRepresentative w F (t,p.2)) p.1) := by
  filter_upwards [MemLp.coeFn_toLp (spectral_cusp_derivative_memLp hF hw henergy)] with p hp
  rw [cuspMeanZeroRepresentative_deriv]
  exact hp

theorem spectral_cusp_toLp_norm_square {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem spectralCuspProjectedLp_norm_square {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    ‖spectralCuspProjectedLp hF hw hY henergy‖^2 =
      ∫ z : UpperHalfPlane in hyperbolicCuspStrip w Y,
        ‖cuspMeanZeroRepresentative w F (z.re,z.im)‖^2 :=
  spectral_cusp_toLp_norm_square _

theorem spectralCuspDerivativeLp_norm_square {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {w Y : ℝ} (hw : 0 < w)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    ‖spectralCuspDerivativeLp hF hw henergy‖^2 =
      ∫ y in Ioi Y, cuspHorizontalEnergy F w y := by
  rw [spectralCuspDerivativeLp, spectral_cusp_toLp_norm_square]
  rw [spectralCuspEuclideanMeasure, integral_prod_symm _
    (spectral_cusp_derivative_sq_integrable hF hw henergy)]
  apply integral_congr_ae
  filter_upwards with y
  simp only [cuspHorizontalEnergy, spectralPlanePartialX,
    intervalIntegral.integral_of_le hw.le]

theorem spectralCuspProjectedLp_norm_le {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (henergy : IntegrableOn (cuspHorizontalEnergy F w) (Ioi Y)) :
    ‖spectralCuspProjectedLp hF hw hY henergy‖ ≤ (w/Y)*‖spectralCuspDerivativeLp hF hw henergy‖ := by
  have hh := hyperbolic_cusp_projected_tail_bound hF.continuous hw hY
    (fun _ _ => hF.comp (contDiff_id.prodMk contDiff_const)) henergy
  rw [← spectralCuspProjectedLp_norm_square hF hw hY henergy,
    ← spectralCuspDerivativeLp_norm_square hF hw henergy] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (div_nonneg hw.le hY.le) (norm_nonneg _))).mp
  calc
    _ ≤ _ := hh
    _ = _ := by ring

/-- The generating functions carry actual smoothness and finite actual
horizontal Dirichlet energy, rather than a postulated graph norm. -/
structure SpectralCuspSmoothCore (w Y : ℝ) where
  toFun : ℝ × ℝ → ℂ
  smooth : ContDiff ℝ ∞ toFun
  energy_integrable : IntegrableOn (cuspHorizontalEnergy toFun w) (Ioi Y)

noncomputable def spectralCuspSmoothGraphPair {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (F : SpectralCuspSmoothCore w Y) :
    Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y)) ×
      Lp ℂ 2 (spectralCuspEuclideanMeasure w Y) :=
  (spectralCuspProjectedLp F.smooth hw hY F.energy_integrable,
    spectralCuspDerivativeLp F.smooth hw F.energy_integrable)

def spectralCuspCompletedGraph {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y) :
    Set (Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y)) ×
      Lp ℂ 2 (spectralCuspEuclideanMeasure w Y)) :=
  closure (range (spectralCuspSmoothGraphPair hw hY))

/-- The cusp-tail estimate extends to the constructed actual L2 graph closure.
The two coordinates retain their invariant and Euclidean measures. -/
theorem spectralCuspCompletedGraph_norm_le {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    {p : Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y)) ×
      Lp ℂ 2 (spectralCuspEuclideanMeasure w Y)}
    (hp : p ∈ spectralCuspCompletedGraph hw hY) : ‖p.1‖ ≤ (w/Y)*‖p.2‖ := by
  have hc : IsClosed {p : Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y)) ×
      Lp ℂ 2 (spectralCuspEuclideanMeasure w Y) | ‖p.1‖ ≤ (w/Y)*‖p.2‖} :=
    isClosed_le continuous_fst.norm (continuous_const.mul continuous_snd.norm)
  apply closure_minimal (t := {p | ‖p.1‖ ≤ (w/Y)*‖p.2‖}) ?_ hc hp
  rintro _ ⟨F,rfl⟩
  exact spectralCuspProjectedLp_norm_le F.smooth hw hY F.energy_integrable

theorem spectralCuspCompletedGraph_isComplete {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y) :
    IsComplete (spectralCuspCompletedGraph hw hY) := isClosed_closure.isComplete

end ArtinMatthews
