module

public import ArtinMatthews.SpectralGamma0CompactInclusion
public import ArtinMatthews.SpectralGamma0CompletedWeakIdentity
public import ArtinMatthews.SpectralGamma0GradientSeparation
public import ArtinMatthews.SpectralModularWeightedTestDensity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Faithfulness of the actual completed Γ₀ mass-plus-gradient form.
The gradient is forced by the mass through the proved weak identity and
actual compact test separation; injectivity is not an extra form axiom. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

/-- An actual completed energy vector with zero mass has zero actual
coordinate gradient, hence vanishes in the completed energy norm. -/
theorem gamma0Energy_eq_zero_of_mass_zero (N : ℕ) [NeZero N]
    (u : gamma0EnergySpace N) (hu : gamma0EnergyInclusion N u = 0) : u = 0 := by
  apply gamma0Energy_eq_zero_of_mass_gradient_zero N u hu
  apply gamma0EnergyGradient_eq_zero_of_charts N u
  intro q i
  apply modular_weighted_test_annihilator_eq_zero q.out (gamma0EnergyGradientChart N q i u)
  intro Y hY φ hφ hs hheight hchart
  exact gamma0Energy_gradient_test_zero_of_mass_zero N u hu q hY φ hφ hs hheight
    (fun p hp => ModularGroup.fdo_subset_fd (hchart p hp)) i

/-- The actual completed mass map is injective. In particular no independent
zero-mass gradient vectors occur in the graph closure. -/
theorem gamma0EnergyInclusion_injective (N : ℕ) [NeZero N] :
    Function.Injective (gamma0EnergyInclusion N) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply gamma0Energy_eq_zero_of_mass_zero N (u-v)
  rw [map_sub,huv,sub_self]

/-- The already proved compact all-height mean-zero mass inclusion is also
faithful. This does not assert density in the full cuspidal mass space. -/
theorem gamma0AllHeightMassInclusion_injective (N : ℕ) [NeZero N] :
    Function.Injective (gamma0AllHeightMassInclusion N) := by
  intro u v huv
  apply Subtype.ext
  exact gamma0EnergyInclusion_injective N huv

end ArtinMatthews
