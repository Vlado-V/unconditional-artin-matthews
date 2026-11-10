module

public import ArtinMatthews.SpectralGamma0WeakInverse
public import ArtinMatthews.SpectralSectionLaplacianSeed
public import ArtinMatthews.SpectralGamma0GlobalDifferentialForm
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

/-! The actual Green operator solves the literal differential equation
against every compact smooth Poincare test, including tests that cross
modular chart boundaries. It inverts the actual mass-plus-Laplacian test. -/

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace ArtinMatthews

theorem gamma0Green_global_weak_laplacian (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (f : Gamma0RegionL2 N) :
    inner ℂ (gamma0SmoothSeedMass N ψ + gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ))
      (gamma0Green N f) = inner ℂ (gamma0SmoothSeedMass N ψ) f := by
  rw [gamma0Green_apply,← gamma0Energy_completed_global_differential_pairing]
  calc
    _ = star (inner ℂ (gamma0WeakSolution N f) (gamma0EnergyTest N ψ)) := by
      simpa only [starRingEnd_apply] using
        (inner_conj_symm (𝕜 := ℂ) (gamma0EnergyTest N ψ) (gamma0WeakSolution N f)).symm
    _ = star (inner ℂ f (gamma0EnergyInclusion N (gamma0EnergyTest N ψ))) := by
      rw [gamma0WeakSolution_equation]
    _ = _ := by
      rw [gamma0EnergyInclusion_test]
      simpa only [starRingEnd_apply] using
        (inner_conj_symm (𝕜 := ℂ) (gamma0SmoothSeedMass N ψ) f)

theorem gamma0Green_compact_seed_inverse (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) :
    gamma0Green N (gamma0SmoothSeedMass N ψ + gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ)) =
      gamma0SmoothSeedMass N ψ := by
  apply (InnerProductSpace.toDual ℂ (Gamma0RegionL2 N)).injective
  ext f
  change inner ℂ (gamma0Green N
    (gamma0SmoothSeedMass N ψ + gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ))) f =
      inner ℂ (gamma0SmoothSeedMass N ψ) f
  exact (gamma0Green_symmetric N _ f).trans (gamma0Green_global_weak_laplacian N ψ f)

end ArtinMatthews
