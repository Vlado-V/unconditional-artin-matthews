module

public import ArtinMatthews.SpectralKLTestSynthesisLinear
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

/-! The actual KL synthesis extended isometrically to the full weighted
spectral L2 space. Dense range in the physical space is not asserted here. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralKLCompletedSynthesis : Lp ℂ 2 spectralKLSpectralMeasure →ₗᵢ[ℂ] Lp ℂ 2 spectralKLPhysicalMeasure :=
  spectralKLTestSynthesisLinear.extendOfIsometry spectralKLTestToLp_denseRange spectralKLTestSynthesis_norm

theorem spectralKLCompletedSynthesis_norm (u : Lp ℂ 2 spectralKLSpectralMeasure) :
    ‖spectralKLCompletedSynthesis u‖ = ‖u‖ := spectralKLCompletedSynthesis.norm_map u

theorem spectralKLCompletedSynthesis_test (g : spectralKLTestSubmodule) :
    spectralKLCompletedSynthesis (spectralKLTestToLp g) = spectralKLTestSynthesis g :=
  LinearMap.extendOfIsometry_eq _ spectralKLTestToLp_denseRange spectralKLTestSynthesis_norm g

theorem spectralKLCompletedSynthesis_test_ae (g : spectralKLTestSubmodule) :
    spectralKLCompletedSynthesis (spectralKLTestToLp g) =ᵐ[spectralKLPhysicalMeasure]
      spectralKLWeightedSynthesis g := by
  rw [spectralKLCompletedSynthesis_test]
  exact spectralKLTestSynthesis_coe g

theorem spectralKLCompletedSynthesis_injective : Function.Injective spectralKLCompletedSynthesis :=
  spectralKLCompletedSynthesis.injective

theorem spectralKLCompletedSynthesis_unique
    (T : Lp ℂ 2 spectralKLSpectralMeasure →ₗᵢ[ℂ] Lp ℂ 2 spectralKLPhysicalMeasure)
    (hT : ∀ g : spectralKLTestSubmodule, T (spectralKLTestToLp g) = spectralKLTestSynthesis g) :
    spectralKLCompletedSynthesis = T := by
  apply LinearMap.extendOfIsometry_unique _ spectralKLTestToLp_denseRange spectralKLTestSynthesis_norm T
  apply LinearMap.ext
  intro g
  exact hT g

end ArtinMatthews
