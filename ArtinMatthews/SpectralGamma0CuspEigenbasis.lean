module

public import ArtinMatthews.SpectralGamma0CuspFormOperator
public import ArtinMatthews.SpectralCompactEigenbasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine Hilbert eigenbasis for the compact Green operator on the
closed mass image of the all-height mean-zero energy space. The codomain is
explicit; no identification with an independently defined full cuspidal
space or a coordinate differential Laplacian is assumed. -/
noncomputable section
open Set Module
open scoped InnerProductSpace
namespace ArtinMatthews

local instance cuspEigenbasis_massInner (N : ℕ) [NeZero N] : Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

abbrev Gamma0AllHeightSpectralIndex (N : ℕ) [NeZero N] :=
  SpectralCompact.CompactSpectralIndex (gamma0AllHeightCoreGreen N)

def gamma0AllHeightSpectralBasis (N : ℕ) [NeZero N] :
    HilbertBasis (Gamma0AllHeightSpectralIndex N) ℂ (gamma0AllHeightEnergyMassSpace N) :=
  SpectralCompact.compactSpectralBasis (gamma0AllHeightCoreGreen N)
    (gamma0AllHeightCoreGreen_compact N) (gamma0AllHeightCoreGreen_symmetric N)

theorem gamma0AllHeightSpectralBasis_eigen (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    gamma0AllHeightCoreGreen N (gamma0AllHeightSpectralBasis N i) =
      i.1 • gamma0AllHeightSpectralBasis N i :=
  SpectralCompact.compactSpectralBasis_eigen _ _ _ i

theorem gamma0AllHeightSpectralValue_ne_zero (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) : i.1 ≠ 0 := by
  intro hi
  have he := gamma0AllHeightSpectralBasis_eigen N i
  rw [hi,zero_smul] at he
  exact (gamma0AllHeightSpectralBasis N).orthonormal.ne_zero i
    ((gamma0AllHeightCoreGreen_eq_zero_iff N _).mp he)

theorem gamma0AllHeightSpectralValue_real (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) : (i.1.re : ℂ) = i.1 := by
  apply RCLike.conj_eq_iff_re.mp
  apply (gamma0AllHeightCoreGreen_symmetric N).conj_eigenvalue_eq_self
  apply Module.End.hasEigenvalue_of_hasEigenvector
  exact ⟨Module.End.mem_eigenspace_iff.mpr (gamma0AllHeightSpectralBasis_eigen N i),
    (gamma0AllHeightSpectralBasis N).orthonormal.ne_zero i⟩

theorem gamma0AllHeightSpectralValue_pos (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) : 0 < i.1.re := by
  have he : inner ℂ (gamma0AllHeightSpectralBasis N i)
      (gamma0AllHeightCoreGreen N (gamma0AllHeightSpectralBasis N i)) = i.1 := by
    rw [gamma0AllHeightSpectralBasis_eigen,
      inner_smul_right (gamma0AllHeightSpectralBasis N i) (gamma0AllHeightSpectralBasis N i) i.1,
      inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (gamma0AllHeightSpectralBasis N i),
      (gamma0AllHeightSpectralBasis N).orthonormal.norm_eq_one i]
    simp
  have hp : 0 ≤ i.1.re := by
    rw [← he,gamma0AllHeightCoreGreen_energy]
    exact sq_nonneg _
  have hn : i.1.re ≠ 0 := by
    intro h
    have hr := gamma0AllHeightSpectralValue_real N i
    rw [h,Complex.ofReal_zero] at hr
    exact gamma0AllHeightSpectralValue_ne_zero N i hr.symm
  exact lt_of_le_of_ne hp hn.symm

theorem gamma0AllHeightSpectralBasis_operator_graph (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0AllHeightSpectralBasis N i, i.1⁻¹ • gamma0AllHeightSpectralBasis N i) ∈
      (gamma0AllHeightMassEnergyOperator N).graph := by
  rw [gamma0AllHeightMassEnergyOperator_graph,map_smul,gamma0AllHeightSpectralBasis_eigen,
    smul_smul,inv_mul_cancel₀ (gamma0AllHeightSpectralValue_ne_zero N i),one_smul]

theorem gamma0AllHeightCoreGreen_eigenspace_finite (N : ℕ) [NeZero N]
    (μ : ℂ) (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (Module.End.eigenspace (gamma0AllHeightCoreGreen N).toLinearMap μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (gamma0AllHeightCoreGreen_compact N) μ hμ

end ArtinMatthews
