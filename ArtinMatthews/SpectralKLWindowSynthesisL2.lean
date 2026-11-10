module

public import ArtinMatthews.SpectralKLCompletedSynthesis
public import ArtinMatthews.SpectralKLInverseIEnvelope
public import ArtinMatthews.SpectralKLAnalysisCalibration
public import ArtinMatthews.SpectralKLInverseIAnalytic
public import ArtinMatthews.SpectralKLNoncompactSynthesis
public import ArtinMatthews.SpectralKLWindowSynthesisBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped ContDiff
noncomputable section

theorem spectralKLWindowData_memLp (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hh : Continuous (fun t : ℝ => h (t : ℂ))) (C : ℝ)
    (hbound : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ C)
    (hg : Continuous g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    MemLp (spectralKLWindowData h g) 2 spectralKLSpectralMeasure := by
  have hm := spectralKLPhysicalAnalysisIntegral_memLp g hg hc hp
  apply hm.of_le_mul (c := C)
    (spectralKLWindowData_continuous h g hh hg hc hp).aestronglyMeasurable
  filter_upwards with t
  rw [spectralKLWindowData, spectralKLCompactOrderTransform_imaginary g hp, norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)

theorem spectralKLWindowSynthesis_measurable (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hh : Continuous (fun t : ℝ => h (t : ℂ)))
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (H : ℝ) (hH : 0 ≤ H) (hbound : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ H * (1 + t ^ 2)) :
    Measurable (spectralKLWindowSynthesis h g) := by
  have hcont := spectralKLWindowSynthesis_continuousOn h g hh hg hc hp H hH hbound
  have hzero : ContinuousOn (spectralKLWindowSynthesis h g) (Ioi (0 : ℝ))ᶜ := by
    apply (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℂ)) ((Ioi (0 : ℝ))ᶜ)).congr
    intro x hx
    change ¬0 < x at hx
    simp only [spectralKLWindowSynthesis, ite_eq_right hx]
  have hm := hcont.measurable_piecewise hzero measurableSet_Ioi
  simpa only [Set.piecewise_same] using hm

theorem spectralKLWindowSynthesis_inverse_ae (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ))) (C : ℝ)
    (hbound : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ C)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    spectralKLCompletedSynthesis
      ((spectralKLWindowData_memLp h g hh.continuous C hbound hg.continuous hc hp).toLp
        (spectralKLWindowData h g)) =ᵐ[spectralKLPhysicalMeasure] spectralKLWindowSynthesis h g := by
  have hC : 0 ≤ C := (norm_nonneg (h 0)).trans (hbound 0)
  have hpoly (t : ℝ) : ‖h (t : ℂ)‖ ≤ C * (1 + t ^ 2) :=
    (hbound t).trans (le_mul_of_one_le_right hC (by nlinarith [sq_nonneg t]))
  have hi (x : ℝ) (hx : 0 < x) : IntegrableOn
      (fun t : ℝ => OAI.CubicEisenstein.schlafliBesselK ((t : ℂ) * Complex.I) x *
        spectralKLWindowData h g t * (spectralKLPlancherelWeight t : ℂ)) (Ioi (0 : ℝ)) :=
    (spectralKLWindowSynthesis_integrable h g hh.continuous hg hc hp C hC hpoly hx).integrableOn
  have ha := spectralKLCompletedSynthesis_integral_ae (spectralKLWindowData h g)
    (spectralKLWindowData_contDiff h g hh hg.continuous hc hp).contDiffOn
    (spectralKLWindowData_memLp h g hh.continuous C hbound hg.continuous hc hp) hi
  filter_upwards [ha, spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx hxp
  simpa only [spectralKLWindowSynthesis, ite_eq_left hxp] using hx

theorem spectralKLWindowSynthesis_memLp (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ))) (C : ℝ)
    (hbound : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ C)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    MemLp (spectralKLWindowSynthesis h g) 2 spectralKLPhysicalMeasure :=
  (memLp_congr_ae (spectralKLWindowSynthesis_inverse_ae h g hh C hbound hg hc hp)).mp (Lp.memLp _)

end
end ArtinMatthews
