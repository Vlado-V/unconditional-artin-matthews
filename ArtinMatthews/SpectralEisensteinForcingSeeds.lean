module

public import ArtinMatthews.SpectralEisensteinForcingCoefficients
public import ArtinMatthews.SpectralEisensteinBoundedLog
public import ArtinMatthews.SpectralEisensteinCompactForcing
public import ArtinMatthews.SpectralBoundedSeedMultiplier
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

/-! Exact fixed-seed decomposition of the original compact forcing. -/
noncomputable section
open Set
open scoped MatrixGroups ContDiff CompactlySupported BoundedContinuousFunction
namespace ArtinMatthews

theorem eisensteinForcingCoefficient0_compact : HasCompactSupport eisensteinForcingCoefficient0 :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) eisensteinForcingCoefficient0_support

theorem eisensteinForcingCoefficient1_compact : HasCompactSupport eisensteinForcingCoefficient1 :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) eisensteinForcingCoefficient1_support

theorem eisensteinForcingCoefficient0_positive_support : tsupport eisensteinForcingCoefficient0 ⊆ Ioi (0:ℝ) :=
  fun _ h => lt_of_lt_of_le (by norm_num) (eisensteinForcingCoefficient0_support h).1

theorem eisensteinForcingCoefficient1_positive_support : tsupport eisensteinForcingCoefficient1 ⊆ Ioi (0:ℝ) :=
  fun _ h => lt_of_lt_of_le (by norm_num) (eisensteinForcingCoefficient1_support h).1

def gamma0EisensteinForcingSeed0 (N : ℕ) [NeZero N] (a : SL(2,ℤ)) : h2SmoothCompactSeeds :=
  cuspHeightProfileSeed N a eisensteinForcingCoefficient0 eisensteinForcingCoefficient0_smooth
    eisensteinForcingCoefficient0_compact eisensteinForcingCoefficient0_positive_support

def gamma0EisensteinForcingSeed1 (N : ℕ) [NeZero N] (a : SL(2,ℤ)) : h2SmoothCompactSeeds :=
  cuspHeightProfileSeed N a eisensteinForcingCoefficient1 eisensteinForcingCoefficient1_smooth
    eisensteinForcingCoefficient1_compact eisensteinForcingCoefficient1_positive_support

theorem gamma0EisensteinForcingSeed_decomposition (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    (cuspHeightProfileSeed N a (eisensteinVerticalCutoffError s)
      (eisensteinVerticalCutoffError_smooth s) (eisensteinVerticalCutoffError_compact s)
      (eisensteinVerticalCutoffError_positive_support s)).val=
    spectralBoundedSeedProduct (gamma0EisensteinForcingSeed0 N a).val
      (spectralBoundedExponential (gamma0SourceBoundedLog N a) s)+
    s • spectralBoundedSeedProduct (gamma0EisensteinForcingSeed1 N a).val
      (spectralBoundedExponential (gamma0SourceBoundedLog N a) s) := by
  ext z
  let H := gamma0SourceHeight N a z
  let B : ℂ := spectralHorizontalPartition (gamma0CuspTrueWidth N a:ℝ) (a • z).re
  change B*eisensteinVerticalCutoffError s H=
    spectralBoundedExponential (gamma0SourceBoundedLog N a) s z*(B*eisensteinForcingCoefficient0 H)+
    s*(spectralBoundedExponential (gamma0SourceBoundedLog N a) s z*(B*eisensteinForcingCoefficient1 H))
  rw [eisensteinVerticalCutoffError_explicit]
  by_cases hH : H ∈ Icc (1:ℝ) 2
  · rw [gamma0SourceBoundedExponential_eq N a s z hH]
    ring
  · have ho : H < 1 ∨ 2 < H := by simpa only [mem_Icc,not_and_or,not_le] using hH
    rw [eisensteinForcingCoefficient0_zero ho,eisensteinForcingCoefficient1_zero ho]
    simp

end ArtinMatthews
