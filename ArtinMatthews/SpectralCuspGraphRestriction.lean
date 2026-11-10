module

public import ArtinMatthews.SpectralCuspGraphCompletion
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual restriction to a higher cusp and the uniform tail estimate on one fixed graph closure. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set

noncomputable def spectralLpMeasureRestriction {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} (h : ν ≤ μ) : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 ν :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using h)

theorem spectralLpMeasureRestriction_ae {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} (h : ν ≤ μ) (f : Lp ℂ 2 μ) :
    spectralLpMeasureRestriction h f =ᵐ[ν] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ _

theorem spectralLpMeasureRestriction_norm_le {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} (h : ν ≤ μ) (f : Lp ℂ 2 μ) :
    ‖spectralLpMeasureRestriction h f‖ ≤ ‖f‖ := by
  have hn : ‖spectralLpMeasureRestriction h‖ ≤ 1 := by
    simpa only [spectralLpMeasureRestriction, ENNReal.toReal_one, Real.one_rpow] using
      (Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) (c := 1)
        (by simp) (by simpa using h))
  exact ((spectralLpMeasureRestriction h).le_opNorm f).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg f))

theorem spectralLpMeasureRestriction_toLp {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} (h : ν ≤ μ) {f : α → ℂ} (hμ : MemLp f 2 μ) (hν : MemLp f 2 ν) :
    spectralLpMeasureRestriction h (hμ.toLp f) = hν.toLp f := by
  apply Lp.ext
  exact (spectralLpMeasureRestriction_ae h _).trans
    (((Measure.absolutelyContinuous_of_le h).ae_eq (MemLp.coeFn_toLp hμ)).trans
      (MemLp.coeFn_toLp hν).symm)

theorem spectralCuspHyperbolicMeasure_mono {w Y₀ Y : ℝ} (hY : Y₀ ≤ Y) :
    volume.restrict (hyperbolicCuspStrip w Y) ≤ volume.restrict (hyperbolicCuspStrip w Y₀) :=
  Measure.restrict_mono_set _ (fun _ hz => ⟨hz.1,hY.trans_lt hz.2⟩)

theorem spectralCuspEuclideanMeasure_mono {w Y₀ Y : ℝ} (hY : Y₀ ≤ Y) :
    spectralCuspEuclideanMeasure w Y ≤ spectralCuspEuclideanMeasure w Y₀ :=
  Measure.prod_mono le_rfl (Measure.restrict_mono_set _ (fun _ hy => hY.trans_lt hy))

def SpectralCuspSmoothCore.restrictHeight {w Y₀ Y : ℝ} (hY : Y₀ ≤ Y)
    (F : SpectralCuspSmoothCore w Y₀) : SpectralCuspSmoothCore w Y where
  toFun := F.toFun
  smooth := F.smooth
  energy_integrable := F.energy_integrable.mono_set (fun _ hy => hY.trans_lt hy)

noncomputable def spectralCuspGraphRestriction {w Y₀ Y : ℝ} (hY : Y₀ ≤ Y)
    (p : Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y₀)) ×
      Lp ℂ 2 (spectralCuspEuclideanMeasure w Y₀)) :
    Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y)) ×
      Lp ℂ 2 (spectralCuspEuclideanMeasure w Y) :=
  (spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY) p.1,
    spectralLpMeasureRestriction (spectralCuspEuclideanMeasure_mono hY) p.2)

theorem spectralCuspGraphRestriction_continuous {w Y₀ Y : ℝ} (hY : Y₀ ≤ Y) :
    Continuous (spectralCuspGraphRestriction (w := w) hY) :=
  ((spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY)).continuous.comp
    continuous_fst).prodMk
    ((spectralLpMeasureRestriction (spectralCuspEuclideanMeasure_mono hY)).continuous.comp
      continuous_snd)

theorem spectralCuspGraphRestriction_smoothPair {w Y₀ Y : ℝ}
    (hw : 0 < w) (hY₀ : 0 < Y₀) (hY : Y₀ ≤ Y) (F : SpectralCuspSmoothCore w Y₀) :
    spectralCuspGraphRestriction hY (spectralCuspSmoothGraphPair hw hY₀ F) =
      spectralCuspSmoothGraphPair hw (hY₀.trans_le hY) (F.restrictHeight hY) := by
  apply Prod.ext
  · exact spectralLpMeasureRestriction_toLp _
      (spectral_cusp_projected_memLp F.smooth hw hY₀ F.energy_integrable)
      (spectral_cusp_projected_memLp F.smooth hw (hY₀.trans_le hY)
        (F.restrictHeight hY).energy_integrable)
  · exact spectralLpMeasureRestriction_toLp _
      (spectral_cusp_derivative_memLp F.smooth hw F.energy_integrable)
      (spectral_cusp_derivative_memLp F.smooth hw (F.restrictHeight hY).energy_integrable)

theorem spectralCuspGraphRestriction_mem_completed {w Y₀ Y : ℝ}
    (hw : 0 < w) (hY₀ : 0 < Y₀) (hY : Y₀ ≤ Y)
    {p : Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y₀)) ×
      Lp ℂ 2 (spectralCuspEuclideanMeasure w Y₀)}
    (hp : p ∈ spectralCuspCompletedGraph hw hY₀) :
    spectralCuspGraphRestriction hY p ∈ spectralCuspCompletedGraph hw (hY₀.trans_le hY) := by
  have hm : MapsTo (spectralCuspGraphRestriction (w := w) hY)
      (range (spectralCuspSmoothGraphPair hw hY₀))
      (range (spectralCuspSmoothGraphPair hw (hY₀.trans_le hY))) := by
    rintro _ ⟨F,rfl⟩
    exact ⟨F.restrictHeight hY, (spectralCuspGraphRestriction_smoothPair hw hY₀ hY F).symm⟩
  exact hm.closure (spectralCuspGraphRestriction_continuous hY) hp

/-- Every element of the one fixed base-height graph completion has the
actual invariant-volume tail bound at every greater height. -/
theorem spectralCuspCompletedGraph_tail_norm_le {w Y₀ Y : ℝ}
    (hw : 0 < w) (hY₀ : 0 < Y₀) (hY : Y₀ ≤ Y)
    {p : Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y₀)) ×
      Lp ℂ 2 (spectralCuspEuclideanMeasure w Y₀)}
    (hp : p ∈ spectralCuspCompletedGraph hw hY₀) :
    ‖spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY) p.1‖ ≤
      (w/Y)*‖p.2‖ := by
  have hh := spectralCuspCompletedGraph_norm_le hw (hY₀.trans_le hY)
    (spectralCuspGraphRestriction_mem_completed hw hY₀ hY hp)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (spectralLpMeasureRestriction_norm_le (spectralCuspEuclideanMeasure_mono hY) p.2)
    (div_nonneg hw.le (hY₀.trans_le hY).le))

theorem spectralCuspCompletedGraph_tail_sq_norm_le {w Y₀ Y : ℝ}
    (hw : 0 < w) (hY₀ : 0 < Y₀) (hY : Y₀ ≤ Y)
    {p : Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y₀)) ×
      Lp ℂ 2 (spectralCuspEuclideanMeasure w Y₀)}
    (hp : p ∈ spectralCuspCompletedGraph hw hY₀) :
    ‖spectralLpMeasureRestriction (spectralCuspHyperbolicMeasure_mono hY) p.1‖^2 ≤
      (w^2/Y^2)*‖p.2‖^2 := by
  have hh := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (div_nonneg hw.le (hY₀.trans_le hY).le) (norm_nonneg _))).mpr
    (spectralCuspCompletedGraph_tail_norm_le hw hY₀ hY hp)
  calc
    _ ≤ _ := hh
    _ = _ := by ring

end ArtinMatthews
