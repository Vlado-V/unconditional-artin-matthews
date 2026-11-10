module

public import ArtinMatthews.SpectralPlaneTestSeed
public import ArtinMatthews.SpectralSectionLaplacian
public import ArtinMatthews.SpectralSeparableLaplacian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Literal compact smooth separable hyperbolic tests, with their support
and actual differential Laplacian discharged from the one-dimensional data. -/

noncomputable section
open Set
open scoped ContDiff

namespace ArtinMatthews

theorem spectralSeparablePlane_support (χ η : ℝ → ℂ) :
    tsupport (fun p : ℝ × ℝ => χ p.1 * η p.2) ⊆ tsupport χ ×ˢ tsupport η := by
  apply closure_minimal _ ((isClosed_tsupport χ).prod (isClosed_tsupport η))
  intro p hp
  exact ⟨subset_tsupport χ (mul_ne_zero_iff.mp hp).1,
    subset_tsupport η (mul_ne_zero_iff.mp hp).2⟩

theorem spectralSeparablePlane_compact (χ η : ℝ → ℂ)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η) :
    HasCompactSupport (fun p : ℝ × ℝ => χ p.1 * η p.2) :=
  (hcχ.prod hcη).of_isClosed_subset (isClosed_tsupport _) (spectralSeparablePlane_support χ η)

def h2SeparableSmoothSeed (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) : h2SmoothCompactSeeds :=
  h2SmoothSeedOfPlane (fun p : ℝ × ℝ => χ p.1 * η p.2)
    ((hχ.comp contDiff_fst).mul (hη.comp contDiff_snd))
    (spectralSeparablePlane_compact χ η hcχ hcη)
    (fun _ hp => hpos (spectralSeparablePlane_support χ η hp).2)

theorem h2SeparableSmoothSeed_apply (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z = χ z.re * η z.im := rfl

theorem h2SeparableSmoothSeed_support (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) :
    tsupport (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val ⊆
      (fun z : UpperHalfPlane => (z.re,z.im)) ⁻¹' (tsupport χ ×ˢ tsupport η) :=
  (h2SmoothSeedOfPlane_support _ _ _ _).trans (preimage_mono (spectralSeparablePlane_support χ η))

theorem h2SeparableSmoothSeed_laplacian (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z =
      -(z.im^2) • (deriv (deriv χ) z.re * η z.im + χ z.re * deriv (deriv η) z.im) :=
  h2SectionPositiveLaplacian_separable χ η hχ hη z

end ArtinMatthews
