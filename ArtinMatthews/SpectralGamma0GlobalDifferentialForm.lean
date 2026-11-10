module

public import ArtinMatthews.SpectralSectionLaplacianSeed
public import ArtinMatthews.SpectralGamma0EnergyGraph
public import ArtinMatthews.SpectralGamma0EnergyDense
public import ArtinMatthews.SpectralGamma0EnergyPairing
public import ArtinMatthews.SpectralGamma0GlobalPairing
public import ArtinMatthews.SpectralPoincareUnfoldingGradient
public import ArtinMatthews.SpectralSectionComplexGreen
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

/-! The actual completed mass-plus-gradient form equals the literal
mass-plus-Laplacian pairing against every compact smooth hyperbolic seed.
The seed may cross chart boundaries; exact arithmetic unfolding supplies
and then cancels the central multiplicity two. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem gamma0SeedGradient_inner_laplacian (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SeedGradient N ψ) (gamma0SeedGradient N φ) =
      inner ℂ (gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ)) (gamma0SmoothSeedMass N φ) := by
  rw [gamma0SeedGradient_inner,gamma0_periodization_unfold_gradient_integral N
    (gamma0PoincareSeed N φ.val) (gamma0PoincareSeed_smooth N φ.val φ.property)
    (gamma0PoincareSeed_invariant N φ.val) ψ,
    ← h2Section_compact_complex_green ψ (gamma0PoincareSeed N φ.val)
      (gamma0PoincareSeed_smooth N φ.val φ.property),gamma0SmoothSeedMass_inner_unfold]
  rfl

theorem gamma0EnergyTest_global_differential_pairing (N : ℕ) [NeZero N]
    (ψ φ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0EnergyTest N ψ) (gamma0EnergyTest N φ) =
      inner ℂ (gamma0SmoothSeedMass N ψ + gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ))
        (gamma0SmoothSeedMass N φ) := by
  rw [gamma0Energy_inner,gamma0EnergyInclusion_test,gamma0EnergyInclusion_test,
    gamma0EnergyGradient_test,gamma0EnergyGradient_test,
    gamma0SeedGradient_inner_laplacian,inner_add_left]

theorem gamma0Energy_completed_global_differential_pairing (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (u : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyTest N ψ) u =
      inner ℂ (gamma0SmoothSeedMass N ψ + gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ))
        (gamma0EnergyInclusion N u) := by
  let A := innerSL ℂ (gamma0EnergyTest N ψ)
  let B := (innerSL ℂ
    (gamma0SmoothSeedMass N ψ + gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ))).comp
      (gamma0EnergyInclusion N)
  have hall : ∀ v : gamma0EnergySpace N, A v = B v := by
    apply isClosed_property (gamma0EnergyTest_dense N) (isClosed_eq A.continuous B.continuous)
    intro φ
    change inner ℂ (gamma0EnergyTest N ψ) (gamma0EnergyTest N φ) =
      inner ℂ (gamma0SmoothSeedMass N ψ + gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ))
        (gamma0EnergyInclusion N (gamma0EnergyTest N φ))
    rw [gamma0EnergyInclusion_test]
    exact gamma0EnergyTest_global_differential_pairing N ψ φ
  exact hall u

end ArtinMatthews
