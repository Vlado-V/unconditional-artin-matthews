module

public import ArtinMatthews.SpectralGamma0CuspHeightRestriction
public import ArtinMatthews.SpectralCompactDenseCore
public import ArtinMatthews.SpectralGamma0CuspMassPositiveHeight
public import ArtinMatthews.SpectralModularDensity
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

/-! Actual all-positive-height cusp restriction on the entire finite-chart
mass Hilbert space, constructed from the proved mass-only bounds and genuine
smooth periodizations of dense range. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

private theorem mass_restriction_exists (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ R : Gamma0RegionL2 N →L[ℂ] CuspHyperbolicL2 (N : ℝ) Y,
      ∀ ψ : h2SmoothCompactSeeds,
        R (gamma0SmoothSeedMass N ψ) = gamma0CuspHeightSeedLinear N r Y hY ψ := by
  obtain ⟨C, _, hb⟩ := gamma0CuspHeightSeedLp_mass_bound N r Y hY
  exact exists_bounded_extension_of_dense_functions (D := h2SmoothCompactSeeds)
    (gamma0CuspHeightSeedLinear N r Y hY) (gamma0SmoothSeedMass N)
    (gamma0SmoothSeedMass_denseRange N)
    (gamma0CuspHeightSeedLinear N r Y hY).map_add
    (gamma0CuspHeightSeedLinear N r Y hY).map_smul
    (gamma0SmoothSeedMass N).map_add (gamma0SmoothSeedMass N).map_smul ⟨C, hb⟩

def gamma0CuspMassRestriction (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    Gamma0RegionL2 N →L[ℂ] CuspHyperbolicL2 (N : ℝ) Y :=
  (mass_restriction_exists N r Y hY).choose

theorem gamma0CuspMassRestriction_apply (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds) :
    gamma0CuspMassRestriction N r Y hY (gamma0SmoothSeedMass N ψ) =
      gamma0CuspHeightSeedLp N r Y hY ψ :=
  (mass_restriction_exists N r Y hY).choose_spec ψ

theorem gamma0CuspMassRestriction_seed_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds) :
    gamma0CuspMassRestriction N r Y hY (gamma0SmoothSeedMass N ψ)
      =ᵐ[volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)] gamma0CuspSection N ψ r := by
  rw [gamma0CuspMassRestriction_apply]
  exact gamma0CuspHeightSeedLp_ae N r Y hY ψ

/-- On the completed energy domain, restriction through the full mass space
equals the previously constructed actual energy-domain restriction. -/
theorem gamma0CuspMassRestriction_energy (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (u : gamma0EnergySpace N) :
    gamma0CuspMassRestriction N r Y hY (gamma0EnergyInclusion N u) =
      gamma0CuspHeightRestriction N r Y hY u := by
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_eq ((gamma0CuspMassRestriction N r Y hY).comp
      (gamma0EnergyInclusion N)).continuous (gamma0CuspHeightRestriction N r Y hY).continuous)
  intro ψ
  change gamma0CuspMassRestriction N r Y hY
    (gamma0EnergyInclusion N (gamma0EnergyTest N ψ)) =
      gamma0CuspHeightRestriction N r Y hY (gamma0EnergyTest N ψ)
  rw [gamma0EnergyInclusion_test, gamma0CuspMassRestriction_apply,
    gamma0CuspHeightRestriction_apply]

end ArtinMatthews
