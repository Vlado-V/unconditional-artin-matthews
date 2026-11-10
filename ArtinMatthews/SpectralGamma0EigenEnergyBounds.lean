module

public import ArtinMatthews.SpectralGamma0CuspActual
public import ArtinMatthews.SpectralGamma0EllipticMassCompletion
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

/-! Quantitative norm identities for the normalized actual cuspidal basis. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

local instance eigenEnergyBounds_massInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

theorem gamma0FullCuspidalSpectralBasis_mass_norm (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    ‖(gamma0FullCuspidalSpectralBasis N i).val‖ = 1 := by
  rw [gamma0FullCuspidalSpectralBasis_coe]
  exact (gamma0AllHeightSpectralBasis N).orthonormal.norm_eq_one i

theorem gamma0AllHeightSpectralEnergy_gradient_norm_sq (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    ‖gamma0EnergyGradient N (gamma0AllHeightSpectralEnergy N i).val‖^2 =
      gamma0AllHeightGradientSpectralValue N i := by
  have he := gamma0AllHeightSpectralEnergy_gradient N i (gamma0AllHeightSpectralEnergy N i)
  rw [gamma0AllHeightSpectralEnergy_mass,
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gamma0AllHeightSpectralBasis N i),
    (gamma0AllHeightSpectralBasis N).orthonormal.norm_eq_one i] at he
  norm_num at he
  exact_mod_cast he

theorem gamma0AllHeightSpectralEnergy_norm_sq (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    ‖(gamma0AllHeightSpectralEnergy N i).val‖^2 =
      1+gamma0AllHeightGradientSpectralValue N i := by
  rw [gamma0Energy_norm_sq,gamma0AllHeightSpectralEnergy_gradient_norm_sq,
    gamma0AllHeightSpectralEnergy_mass_ambient]
  have hn : ‖(gamma0AllHeightSpectralBasis N i).val‖ = 1 :=
    (gamma0AllHeightSpectralBasis N).orthonormal.norm_eq_one i
  rw [hn,one_pow]

theorem gamma0AllHeightSpectralEnergy_norm_le (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    ‖(gamma0AllHeightSpectralEnergy N i).val‖ ≤
      1+gamma0AllHeightGradientSpectralValue N i := by
  have hp := gamma0AllHeightGradientSpectralValue_nonneg N i
  apply (sq_le_sq₀ (norm_nonneg _) (by linarith)).mp
  rw [gamma0AllHeightSpectralEnergy_norm_sq]
  nlinarith

theorem gamma0EllipticEigenPair_norm_le
    (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
    (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (r : SL(2,ℤ)) (L : ℂ →L[ℝ] ℝ) (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    ‖gamma0EllipticPair φ ha hφ r L N (gamma0AllHeightSpectralEnergy N i).val‖ ≤
      ‖gamma0EllipticPair φ ha hφ r L N‖ * (1+gamma0AllHeightGradientSpectralValue N i) :=
  ((gamma0EllipticPair φ ha hφ r L N).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (gamma0AllHeightSpectralEnergy_norm_le N i)
      (ContinuousLinearMap.opNorm_nonneg _))

theorem gamma0EllipticEigenPair_mass_norm_le
    (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (r : SL(2,ℤ)) (L : ℂ →L[ℝ] ℝ) (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    ‖(gamma0EllipticPair φ ha hφ r L N (gamma0AllHeightSpectralEnergy N i).val).1‖ ≤
      ‖gamma0EllipticMass φ ha hφ r L N‖ := by
  rw [← gamma0EllipticMass_energy φ ha hab hφ r L N,
    gamma0AllHeightSpectralEnergy_mass_ambient]
  have hm := (gamma0EllipticMass φ ha hφ r L N).le_opNorm (gamma0AllHeightSpectralBasis N i).val
  have hn : ‖(gamma0AllHeightSpectralBasis N i).val‖ = 1 :=
    (gamma0AllHeightSpectralBasis N).orthonormal.norm_eq_one i
  simpa only [hn,mul_one] using hm

end ArtinMatthews
