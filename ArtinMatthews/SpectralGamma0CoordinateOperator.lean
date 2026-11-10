module

public import ArtinMatthews.SpectralGamma0FormOperator
public import ArtinMatthews.SpectralSectionLaplacianSeed
public import ArtinMatthews.SpectralGamma0GlobalWeakLaplacian
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

/-! The genuine represented self-adjoint operator agrees with the literal
mass-plus-hyperbolic-Laplacian on every actual compact smooth Poincare seed. -/

noncomputable section
namespace ArtinMatthews

theorem gamma0MassEnergyOperator_compact_seed_graph (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) :
    (gamma0SmoothSeedMass N ψ,
      gamma0SmoothSeedMass N ψ + gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ)) ∈
      (gamma0MassEnergyOperator N).graph :=
  (gamma0MassEnergyOperator_graph N _ _).mpr (gamma0Green_compact_seed_inverse N ψ)

end ArtinMatthews
