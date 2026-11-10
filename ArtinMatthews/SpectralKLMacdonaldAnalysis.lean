module

public import ArtinMatthews.SpectralKLMacdonaldProfile
public import ArtinMatthews.SpectralKLUnitary
public import ArtinMatthews.SpectralKLIntegrableCalibration
public import ArtinMatthews.SpectralKLMacdonaldMajorant
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The completed KL analysis of the actual noncompact Gaussian-Weyl
profile is the genuine product of K kernels.  All L2 and L1 hypotheses
are supplied by the proved heat/Macdonald integrals. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralKLMacdonaldProfile_completed_analysis {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    spectralKLAnalysis ((spectralKLMacdonaldProfile_memLp hx hy).toLp (spectralKLMacdonaldProfile x y))
      =ᵐ[spectralKLSpectralMeasure]
        (fun t : ℝ => 2*schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((t : ℂ)*Complex.I) y) := by
  have h := spectralKLAnalysis_majorant_ae (spectralKLMacdonaldProfile x y)
    (spectralKLMacdonaldProfile_measurable x y) (spectralKLMacdonaldProfile_nonpositive_zero x y)
    (spectralKLMacdonaldProfile_majorant_integrable hx hy) (spectralKLMacdonaldProfile_memLp hx hy)
  exact h.trans (Filter.Eventually.of_forall (spectralKLMacdonaldProfile_literal_analysis hx hy))

theorem spectralKLMacdonaldProduct_memLp {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    MemLp (fun t : ℝ => 2*schlafliBesselK ((t : ℂ)*Complex.I) x*
      schlafliBesselK ((t : ℂ)*Complex.I) y) 2 spectralKLSpectralMeasure :=
  (memLp_congr_ae (spectralKLMacdonaldProfile_completed_analysis hx hy)).mp (Lp.memLp _)

theorem spectralKLMacdonaldProduct_completed_synthesis {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    spectralKLCompletedSynthesis ((spectralKLMacdonaldProduct_memLp hx hy).toLp
      (fun t : ℝ => 2*schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((t : ℂ)*Complex.I) y)) =
      (spectralKLMacdonaldProfile_memLp hx hy).toLp (spectralKLMacdonaldProfile x y) := by
  have hLp : (spectralKLMacdonaldProduct_memLp hx hy).toLp
      (fun t : ℝ => 2*schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((t : ℂ)*Complex.I) y) =
      spectralKLAnalysis ((spectralKLMacdonaldProfile_memLp hx hy).toLp (spectralKLMacdonaldProfile x y)) := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (spectralKLMacdonaldProfile_completed_analysis hx hy).symm
  rw [hLp,spectralKLSynthesis_analysis]

end ArtinMatthews
