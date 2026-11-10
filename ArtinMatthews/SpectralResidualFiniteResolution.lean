module

public import ArtinMatthews.SpectralResidualFiniteEnergies
public import ArtinMatthews.SpectralStoneEisensteinSesquilinear
public import ArtinMatthews.SpectralStoneNativePairing
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

/-! The residual part of the actual compact spectral resolution is a
finite sum at fixed level, with every projection retained explicitly. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

def gamma0ResidualEnergyWindow (N : ℕ) [NeZero N] : Finset (Ici (0:ℝ)) :=
  ((gamma0ResidualEnergyCandidates_finite N).preimage Subtype.val_injective.injOn).toFinset

theorem mem_gamma0ResidualEnergyWindow (N : ℕ) [NeZero N] (l : Ici (0:ℝ)) :
    l∈gamma0ResidualEnergyWindow N ↔ (l:ℝ)∈gamma0ResidualEnergyCandidates N :=
  Set.Finite.mem_toFinset _

theorem gamma0StoneResidualPair_eq_finite (N : ℕ) [NeZero N] (u v : Gamma0RegionL2 N) :
    gamma0StoneResidualPair N u v=
      ∑ l∈gamma0ResidualEnergyWindow N,
        inner ℂ (gamma0AmbientResidualProjection N (l:ℝ) u) (gamma0AmbientResidualProjection N (l:ℝ) v) := by
  unfold gamma0StoneResidualPair
  apply tsum_eq_sum
  intro l hl
  have hn : (l:ℝ)∉gamma0ResidualEnergyCandidates N := mt (mem_gamma0ResidualEnergyWindow N l).mpr hl
  rw [gamma0AmbientResidualProjection_zero_off_finite N (l:ℝ) l.property hn u,inner_zero_left]

theorem gamma0CompactStoneNativePairing_finiteResidual (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0SmoothSeedMass N ξ)=
      (∑' i : Gamma0AllHeightSpectralIndex N,
        inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0FullCuspidalSpectralBasis N i).val*
          inner ℂ (gamma0FullCuspidalSpectralBasis N i).val (gamma0SmoothSeedMass N ξ))+
      (gamma0StoneEisensteinPair N ψ ξ+
        ∑ l∈gamma0ResidualEnergyWindow N,
          inner ℂ (gamma0AmbientResidualProjection N (l:ℝ) (gamma0SmoothSeedMass N ψ))
            (gamma0AmbientResidualProjection N (l:ℝ) (gamma0SmoothSeedMass N ξ))) := by
  rw [gamma0CompactStoneNativePairing N ψ ξ,gamma0StoneResidualPair_eq_finite]

end ArtinMatthews
