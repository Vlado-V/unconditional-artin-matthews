module

public import ArtinMatthews.SpectralEisensteinForcingSeeds
public import ArtinMatthews.SpectralBoundedSeedExponential
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

/-! Entire dependence of the actual compact Eisenstein forcing in the full
ambient L² space, via its proved fixed-seed decomposition. -/
noncomputable section
open scoped MatrixGroups CompactlySupported
namespace ArtinMatthews

def gamma0EisensteinForcingAnalyticFamily (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ) :
    Gamma0RegionL2 N :=
  (1/2:ℂ) • (gamma0BoundedSeedExponentialMass N (gamma0EisensteinForcingSeed0 N a).val
    (gamma0SourceBoundedLog N a) s+
    s • gamma0BoundedSeedExponentialMass N (gamma0EisensteinForcingSeed1 N a).val
      (gamma0SourceBoundedLog N a) s)

theorem gamma0CuspEisensteinCompactForcingMass_eq_analytic (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) :
    gamma0CuspEisensteinCompactForcingMass N a s=gamma0EisensteinForcingAnalyticFamily N a s := by
  change gamma0SeedMass N ((1/2:ℂ) •
    (cuspHeightProfileSeed N a (eisensteinVerticalCutoffError s)
      (eisensteinVerticalCutoffError_smooth s) (eisensteinVerticalCutoffError_compact s)
      (eisensteinVerticalCutoffError_positive_support s)).val)=_
  rw [map_smul,gamma0EisensteinForcingSeed_decomposition,map_add,map_smul]
  rfl

theorem gamma0CuspEisensteinCompactForcingMass_analyticAt (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) : AnalyticAt ℂ (gamma0CuspEisensteinCompactForcingMass N a) s := by
  have he : gamma0CuspEisensteinCompactForcingMass N a=gamma0EisensteinForcingAnalyticFamily N a :=
    funext (gamma0CuspEisensteinCompactForcingMass_eq_analytic N a)
  rw [he]
  have h0 := gamma0BoundedSeedExponentialMass_analyticAt N (gamma0EisensteinForcingSeed0 N a).val
    (gamma0SourceBoundedLog N a) s
  have h1 := gamma0BoundedSeedExponentialMass_analyticAt N (gamma0EisensteinForcingSeed1 N a).val
    (gamma0SourceBoundedLog N a) s
  exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1/2:ℂ)) s).smul
    (h0.add ((analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) s).smul h1))

end ArtinMatthews
