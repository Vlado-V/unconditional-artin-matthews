module

public import ArtinMatthews.SpectralKLCutoffConvergence
public import ArtinMatthews.SpectralKLAnalysisCalibration
public import ArtinMatthews.SpectralWeylCutoffCompact
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

/-! The completed KL analysis of every literal compact cutoff agrees
with its proved integral formula. The uncut input is an actual L2
function and no pointwise inverse representation is assumed. -/

noncomputable section
open Set MeasureTheory Filter
namespace ArtinMatthews

theorem spectralKLAnalysis_height_cutoff_ae {a : ℝ} (ha : 0 < a) (K : ℕ)
    (f : ℝ → ℂ) (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (hL : MemLp f 2 spectralKLPhysicalMeasure) :
    spectralKLAnalysis (spectralWeylCutoffLp a K (hL.toLp f)) =ᵐ[spectralKLSpectralMeasure]
      spectralKLPhysicalAnalysisIntegral (spectralWeylProfileCutoff a K f) := by
  let g := spectralWeylProfileCutoff a K f
  have hc : Continuous g := spectralWeylProfileCutoff_continuous ha K f hf
  have hs : HasCompactSupport g := spectralWeylProfileCutoff_compact ha K f
  have hp : tsupport g ⊆ Ioi (0 : ℝ) := spectralWeylProfileCutoff_positive ha K f
  have hg := spectralKLPhysical_compact_memLp g hc hs hp
  have he : spectralWeylCutoffLp a K (hL.toLp f) = hg.toLp g := by
    apply Lp.ext
    filter_upwards [spectralWeylCutoffLp_ae a K (hL.toLp f),hL.coeFn_toLp,hg.coeFn_toLp]
      with x hx hf' hg'
    rw [hx,hg']
    change (spectralHeightAnnularPartial K (a*x) : ℂ)*(hL.toLp f) x =
      (spectralHeightAnnularPartial K (a*x) : ℂ)*f x
    rw [hf']
  rw [he]
  exact spectralKLAnalysis_compact_ae g hc hs hp

end ArtinMatthews
