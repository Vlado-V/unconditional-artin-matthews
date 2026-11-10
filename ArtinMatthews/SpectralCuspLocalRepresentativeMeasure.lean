module

public import ArtinMatthews.SpectralCuspLocalSmoothExtension
public import ArtinMatthews.CuspAverageProjectionBase
public import ArtinMatthews.SpectralCuspTwoCellHyperbolic
public import ArtinMatthews.SpectralCuspTwoCellRepresentative
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

/-! Ordinary local almost-everywhere representatives on the open two-cell
strip represent the actual weighted strip L² class. Boundary lines are null. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace ArtinMatthews

theorem cuspStripMeasure_absolutelyContinuous_volume (w Y : ℝ) :
    cuspStripMeasure w Y ≪ (volume : Measure (ℝ × ℝ)) := by
  have hh : cuspHorizontalMeasure w ≪ (volume : Measure ℝ) :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hv : cuspVerticalMeasure Y ≪ (volume : Measure ℝ) :=
    (withDensity_absolutelyContinuous (volume.restrict (Ioi Y)) _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  exact hh.prod hv

theorem cuspStripMeasure_openTwoCell_ae (N Y : ℝ) (hY : 0 < Y) :
    ∀ᵐ p ∂cuspStripMeasure (2 * N) Y, p ∈ spectralOpenTwoCell N Y := by
  have hxne : ∀ᵐ x ∂cuspHorizontalMeasure (2 * N), x ≠ 2 * N :=
    ae_restrict_of_ae (volume.ae_ne (2 * N))
  have hn := (Measure.quasiMeasurePreserving_fst (μ := cuspHorizontalMeasure (2 * N))
    (ν := cuspVerticalMeasure Y)).ae hxne
  filter_upwards [cuspStripMeasure_first_mem (2 * N) Y, cuspStripMeasure_height_mem hY (2 * N), hn]
    with p hx hy hne
  refine ⟨hx.1, ?_, hy⟩
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · exact hlt
  · exact (hne heq).elim

theorem cuspStripMeasure_local_ae (N Y : ℝ) (hY : 0 < Y)
    {P : (ℝ × ℝ) → Prop}
    (hP : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ spectralOpenTwoCell N Y → P p) :
    ∀ᵐ p ∂cuspStripMeasure (2 * N) Y, P p := by
  have h := hP.filter_mono (cuspStripMeasure_absolutelyContinuous_volume (2 * N) Y).ae_le
  filter_upwards [h, cuspStripMeasure_openTwoCell_ae N Y hY] with p hp hmem
  exact hp hmem

end ArtinMatthews
