module

public import ArtinMatthews.SpectralJGaussianFubini
public import ArtinMatthews.SpectralJGaussianTail
public import ArtinMatthews.SpectralKLUnitary
public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralJGaussianDecay
public import ArtinMatthews.SpectralJGaussianProbeKL
public import ArtinMatthews.SpectralJGaussianRealCoefficient
public import ArtinMatthews.SpectralJGaussianTailAnalysis
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

/-! The normalized tail has the actual native coefficient in completed KL space. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ContDiff
noncomputable section

theorem spectralJGaussianTail_normalized_completed_analysis (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi (0 : ℝ)) :
    let G := fun y : ℝ => (1 / (Real.sqrt (8 * Real.pi) : ℂ)) *
      spectralJGaussianTail (spectralJGaussianTransform f) y
    ∃ hG : MemLp G 2 spectralKLPhysicalMeasure,
      spectralKLAnalysis (hG.toLp G) =ᵐ[spectralKLSpectralMeasure] fun r : ℝ =>
        (∫ x : ℝ in Ioi 0, f x * spectralWeylJMultiplier r x) /
          (4 * (Real.cosh (Real.pi * r) : ℂ)) := by
  let F := spectralJGaussianTransform f
  let G := spectralJGaussianTail F
  let c : ℂ := 1 / (Real.sqrt (8 * Real.pi) : ℂ)
  have hfi : IntegrableOn f (Ioi (0 : ℝ)) :=
    (hf.continuous.integrable_of_hasCompactSupport hfc).integrableOn
  have hFm := (spectralJGaussianTransform_continuous f hf.continuous hfi).measurable
  have hFi := spectralJGaussianTransform_integrableOn_tail f hf hfc hpos
  have hG : MemLp G 2 spectralKLPhysicalMeasure := spectralJGaussianTail_memLp F hFm hFi
  refine ⟨hG.const_smul c, ?_⟩
  change spectralKLAnalysis ((hG.const_smul c).toLp (c • G)) =ᵐ[spectralKLSpectralMeasure] _
  rw [MemLp.toLp_const_smul c hG, map_smul]
  filter_upwards [Lp.coeFn_smul c (spectralKLAnalysis (hG.toLp G)),
    spectralJGaussianTail_completed_analysis F hFm hFi,
    spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with r hscale hraw hr
  rw [hscale]
  change c * spectralKLAnalysis (hG.toLp G) r = _
  rw [hraw, spectralJGaussianTail_analysisIntegral_eq]
  have he := spectralJGaussianTail_real_coefficient f hf hfc hpos r hr
  rw [← he]
  dsimp only [c]
  ring

end
end ArtinMatthews
