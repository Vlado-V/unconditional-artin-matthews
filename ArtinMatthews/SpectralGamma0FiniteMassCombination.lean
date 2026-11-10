module

public import ArtinMatthews.SpectralGamma0CuspActual
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite real combinations of the normalized complex cuspidal basis. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_ambient_orthonormal (N : ℕ) [NeZero N] :
    Orthonormal ℂ (fun i => (gamma0FullCuspidalSpectralBasis N i).val) := by
  have h := (gamma0AllHeightSpectralBasis N).orthonormal.comp_linearIsometry
    (gamma0AllHeightEnergyMassSpace N).subtypeₗᵢ
  change Orthonormal ℂ (fun i => (gamma0AllHeightSpectralBasis N i).val) at h
  simpa only [gamma0FullCuspidalSpectralBasis_coe] using h

def gamma0FiniteMassCombination (N : ℕ) [NeZero N]
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    Gamma0RegionL2 N := ∑ i ∈ s, (c i : ℂ) • (gamma0FullCuspidalSpectralBasis N i).val

theorem gamma0FiniteMassCombination_eq_real_sum (N : ℕ) [NeZero N]
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    gamma0FiniteMassCombination N s c = ∑ i ∈ s, c i • (gamma0FullCuspidalSpectralBasis N i).val := by
  exact Finset.sum_congr rfl (fun i _ => IsScalarTower.algebraMap_smul ℂ (c i) _)

theorem gamma0FiniteMassCombination_norm_sq (N : ℕ) [NeZero N]
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    ‖gamma0FiniteMassCombination N s c‖^2 = ∑ i ∈ s, (c i)^2 := by
  have hi := (gamma0FullCuspidalSpectralBasis_ambient_orthonormal N).inner_sum
    (fun i => (c i : ℂ)) (fun i => (c i : ℂ)) s
  change inner ℂ (gamma0FiniteMassCombination N s c) (gamma0FiniteMassCombination N s c) = _ at hi
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gamma0FiniteMassCombination N s c)] at hi
  have hr := congrArg Complex.re hi
  simpa [pow_two] using hr

theorem gamma0Green_finiteMassCombination (N : ℕ) [NeZero N]
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    gamma0Green N (gamma0FiniteMassCombination N s c) =
      gamma0FiniteMassCombination N s (fun i => i.1.re*c i) := by
  simp only [gamma0FiniteMassCombination,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [gamma0FullCuspidalSpectralBasis_eigen,← gamma0AllHeightSpectralValue_real N i,smul_smul]
  congr 1
  push_cast
  simp only [Complex.ofReal_re]
  ring

end ArtinMatthews
