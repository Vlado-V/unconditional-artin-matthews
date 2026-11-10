module

public import ArtinMatthews.SpectralEnergyTest
public import ArtinMatthews.SpectralEisensteinAmbientResolution
public import ArtinMatthews.SpectralResidualEigenbasis
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

/-! Energy tests on the genuine finite residual spectrum. Each retained
term is the actual orthogonal residual eigenspace projection. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

theorem gamma0ResidualProjection_pair (N : ℕ) [NeZero N] (l : Ici (0:ℝ))
    (u v : Gamma0RegionL2 N) :
    inner ℂ u (gamma0AmbientResidualProjection N l v)=
      inner ℂ (gamma0AmbientResidualProjection N l u) (gamma0AmbientResidualProjection N l v) := by
  let U := gamma0ResidualEnergyEigenspace N l
  rw [gamma0AmbientResidualProjection_eq_orthogonalProjection,gamma0AmbientResidualProjection_eq_orthogonalProjection]
  have hi := U.inner_starProjection_left_eq_right u (U.starProjection v)
  rw [Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem v)] at hi
  exact hi.symm

def gamma0ResidualTestOperator (N : ℕ) [NeZero N] (h : SpectralEnergyTest) :
    Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  ∑ l∈gamma0ResidualEnergyWindow N,h l • gamma0AmbientResidualProjection N l

theorem gamma0ResidualTestOperator_pair (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (u v : Gamma0RegionL2 N) :
    inner ℂ u (gamma0ResidualTestOperator N h v)=
      ∑ l∈gamma0ResidualEnergyWindow N,h l*
        ∑ j,inner ℂ u (gamma0ResidualEigenbasis N l j).val*
          inner ℂ (gamma0ResidualEigenbasis N l j).val v := by
  rw [gamma0ResidualTestOperator,sum_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_apply,inner_smul_right,gamma0ResidualProjection_pair,gamma0AmbientResidualProjection_basis_pairing]

theorem gamma0ResidualTestOperator_green (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0ResidualTestOperator N spectralGreenEnergyTest u=gamma0Green N (gamma0ResidualProjection N u) := by
  rw [gamma0ResidualTestOperator,sum_apply,gamma0ResidualProjection,sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_apply,spectralGreenEnergyTest_apply,gamma0EnergyGreenWeight_eq_real]
  exact ((mem_gamma0AmbientEnergyEigenspace_iff N l _).mp (gamma0AmbientResidualProjection_mem N l u).1).symm

end ArtinMatthews
