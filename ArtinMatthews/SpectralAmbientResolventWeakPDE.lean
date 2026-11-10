module

public import ArtinMatthews.SpectralEisensteinContinuation
public import ArtinMatthews.SpectralSectionLaplacianSeed
public import ArtinMatthews.SpectralGamma0GlobalDifferentialForm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual ambient resolvent solves the literal differential equation
against every compact smooth seed. No cusp projection is used. -/
noncomputable section
open scoped InnerProductSpace MatrixGroups
namespace ArtinMatthews

theorem gamma0EnergyGradient_completed_differential_pairing (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (u : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyGradient N (gamma0EnergyTest N ψ)) (gamma0EnergyGradient N u)=
      inner ℂ (gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ)) (gamma0EnergyInclusion N u) := by
  have he := gamma0Energy_completed_global_differential_pairing N ψ u
  rw [gamma0FormEnergy_inner,gamma0EnergyInclusion_test,inner_add_left] at he
  exact add_left_cancel he

theorem gamma0AmbientResolvent_global_weak_laplacian (N : ℕ) [NeZero N]
    (eig : ℂ) (heig : eig.re < ‖eig‖) (F : Gamma0RegionL2 N) (ψ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ))
        (gamma0AmbientResolventFamily N eig F)-
      eig*inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0AmbientResolventFamily N eig F)=
        inner ℂ (gamma0SmoothSeedMass N ψ) F := by
  rw [gamma0AmbientResolventFamily_eq N eig heig]
  have he := gamma0AmbientWeakResolvent_equation N eig heig F (gamma0EnergyTest N ψ)
  rw [gamma0EnergyGradient_completed_differential_pairing,gamma0EnergyInclusion_test] at he
  exact he

theorem gamma0CuspEisensteinContinuedRemainder_global_weak_laplacian
    (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (hs : s ∈ gamma0EisensteinContinuationDomain) (ψ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ))
        (gamma0CuspEisensteinContinuedRemainder N a s)-
      (s*(1-s))*inner ℂ (gamma0SmoothSeedMass N ψ)
        (gamma0CuspEisensteinContinuedRemainder N a s)=
      -inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0CuspEisensteinCompactForcingMass N a s) := by
  simpa only [gamma0CuspEisensteinContinuedRemainder,inner_neg_right] using
    gamma0AmbientResolvent_global_weak_laplacian N (s*(1-s)) hs.2
      (-gamma0CuspEisensteinCompactForcingMass N a s) ψ

end ArtinMatthews
