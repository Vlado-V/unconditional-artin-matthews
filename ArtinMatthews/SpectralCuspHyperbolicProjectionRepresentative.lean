module

public import ArtinMatthews.SpectralCuspHyperbolicProjection
public import ArtinMatthews.CuspAverageProjection
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
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
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
public import Mathlib.Topology.UniformSpace.Uniformizable


set_option backward.privateInPublic true
@[expose] public section

/-! Literal representatives of the hyperbolic average projection. Product
membership is derived from actual invariant-measure L2 membership, and
horizontal means are transferred using Fubini rather than point evaluation. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory Set
open scoped ENNReal

theorem cuspHyperbolic_memLp_iff (w Y : ℝ) (hY : 0 < Y)
    (F : ℝ × ℝ → ℂ) (hF : Continuous F) :
    MemLp F 2 (cuspStripMeasure w Y) ↔
      MemLp (fun z : UpperHalfPlane => F (z.re,z.im)) 2
        (volume.restrict (hyperbolicCuspStrip w Y)) := by
  have hmp := cusp_coordinates_measurePreserving w Y hY
  have hm : AEStronglyMeasurable F
      (Measure.map (fun z : UpperHalfPlane => (z.re,z.im))
        (volume.restrict (hyperbolicCuspStrip w Y))) := by
    rw [hmp.map_eq]
    exact hF.aestronglyMeasurable
  have h := memLp_map_measure_iff (p := (2 : ℝ≥0∞)) hm hmp.aemeasurable
  simpa only [hmp.map_eq, Function.comp_def] using h

theorem cuspHorizontalMean_congr_ae (w Y : ℝ) {F G : ℝ × ℝ → ℂ}
    (hFG : F =ᵐ[cuspStripMeasure w Y] G) :
    cuspHorizontalMean w F =ᵐ[cuspVerticalMeasure Y] cuspHorizontalMean w G := by
  have hs := (Measure.measurePreserving_swap (μ := cuspVerticalMeasure Y)
    (ν := cuspHorizontalMeasure w)).quasiMeasurePreserving.ae_eq_comp hFG
  have hxy := Measure.ae_ae_of_ae_prod hs
  filter_upwards [hxy] with y hy
  have he : (fun x : ℝ => F (x,y)) =ᵐ[cuspHorizontalMeasure w] (fun x : ℝ => G (x,y)) := hy
  unfold cuspHorizontalMean
  exact congrArg (fun z : ℂ => (w : ℂ)⁻¹*z) (integral_congr_ae he)

theorem cuspAverageRepresentative_congr_ae (w Y : ℝ) {F G : ℝ × ℝ → ℂ}
    (hFG : F =ᵐ[cuspStripMeasure w Y] G) :
    cuspAverageRepresentative w F =ᵐ[cuspStripMeasure w Y] cuspAverageRepresentative w G := by
  have hm := cuspHorizontalMean_congr_ae w Y hFG
  let hmp : MeasurePreserving Prod.snd (cuspStripMeasure w Y)
      ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) :=
    ⟨measurable_snd, Measure.map_snd_prod⟩
  have hm' := Measure.ae_smul_measure hm (cuspHorizontalMeasure w univ)
  exact hmp.quasiMeasurePreserving.ae_eq_comp hm'

theorem cuspHyperbolicPullback_toLp (w Y : ℝ) (hY : 0 < Y) (F : ℝ × ℝ → ℂ)
    (hp : MemLp F 2 (cuspStripMeasure w Y))
    (hh : MemLp (fun z : UpperHalfPlane => F (z.re,z.im)) 2
      (volume.restrict (hyperbolicCuspStrip w Y))) :
    cuspHyperbolicPullback w Y hY (hp.toLp F) = hh.toLp (fun z : UpperHalfPlane => F (z.re,z.im)) := by
  apply Lp.ext
  exact (cuspHyperbolicPullback_ae w Y hY _).trans
    (((cusp_coordinates_measurePreserving w Y hY).quasiMeasurePreserving.ae_eq_comp hp.coeFn_toLp).trans
      hh.coeFn_toLp.symm)

/-- The transported Hilbert projection agrees with the normalized literal
horizontal integral of the given continuous plane function. -/
theorem cuspHyperbolicAverageProjection_ae_representative (w Y : ℝ)
    (hw : 0 < w) (hY : 0 < Y) (F : ℝ × ℝ → ℂ) (hF : Continuous F)
    (hh : MemLp (fun z : UpperHalfPlane => F (z.re,z.im)) 2
      (volume.restrict (hyperbolicCuspStrip w Y))) :
    cuspHyperbolicAverageProjection w Y hY (hh.toLp (fun z : UpperHalfPlane => F (z.re,z.im)))
      =ᵐ[volume.restrict (hyperbolicCuspStrip w Y)]
        (fun z : UpperHalfPlane => cuspAverageRepresentative w F (z.re,z.im)) := by
  have hp := (cuspHyperbolic_memLp_iff w Y hY F hF).mpr hh
  rw [← cuspHyperbolicPullback_toLp w Y hY F hp hh, cuspHyperbolicAverageProjection_pullback]
  have hproj := cuspAverageProjection_ae_representative w Y hw (hp.toLp F)
  have havg := cuspAverageRepresentative_congr_ae w Y hp.coeFn_toLp
  exact (cuspHyperbolicPullback_ae w Y hY _).trans
    ((cusp_coordinates_measurePreserving w Y hY).quasiMeasurePreserving.ae_eq_comp (hproj.trans havg))

theorem cuspHyperbolicMeanZero_ae_representative (w Y : ℝ)
    (hw : 0 < w) (hY : 0 < Y) (F : ℝ × ℝ → ℂ) (hF : Continuous F)
    (hh : MemLp (fun z : UpperHalfPlane => F (z.re,z.im)) 2
      (volume.restrict (hyperbolicCuspStrip w Y))) :
    ((hh.toLp (fun z : UpperHalfPlane => F (z.re,z.im)))-
      cuspHyperbolicAverageProjection w Y hY (hh.toLp (fun z : UpperHalfPlane => F (z.re,z.im))))
      =ᵐ[volume.restrict (hyperbolicCuspStrip w Y)]
        (fun z : UpperHalfPlane => cuspMeanZeroRepresentative w F (z.re,z.im)) := by
  filter_upwards [Lp.coeFn_sub (hh.toLp (fun z : UpperHalfPlane => F (z.re,z.im)))
      (cuspHyperbolicAverageProjection w Y hY (hh.toLp (fun z : UpperHalfPlane => F (z.re,z.im)))),
    hh.coeFn_toLp, cuspHyperbolicAverageProjection_ae_representative w Y hw hY F hF hh]
      with z hsub hvalue havg
  simpa only [Pi.sub_apply, hvalue, havg, cuspMeanZeroRepresentative] using hsub

end
end ArtinMatthews
