module

public import ArtinMatthews.SpectralEisensteinCompactProfileSeed
public import ArtinMatthews.SpectralGamma0EnergyGraph
public import ArtinMatthews.SpectralModularDensityPeriodization
public import ArtinMatthews.SpectralPoincareLinear
public import Mathlib.Algebra.FiniteSupport.Basic
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

/-! A compact normalized height profile is an actual compact-seed
periodization, hence an actual vector in the full completed energy graph. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff CompactlySupported
namespace ArtinMatthews

theorem gamma0CompactSeed_point_finite (N : ℕ) [NeZero N]
    (ψ : C_c(UpperHalfPlane,ℂ)) (z : UpperHalfPlane) :
    Function.HasFiniteSupport (fun γ : CongruenceSubgroup.Gamma0 N => ψ (γ.val • z)) := by
  let e := (CongruenceSubgroup.Gamma0 N).equivMapOfInjective
    (Matrix.SpecialLinearGroup.mapGL ℝ) (Matrix.SpecialLinearGroup.mapGL_injective (S := ℝ))
  have h : Function.HasFiniteSupport (fun g : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) =>
      ψ (g • z)) :=
    (arithmetic_poincare_support_locallyFinite
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ψ).point_finite z
  exact Function.HasFiniteSupport.fun_comp_of_injective
    (f := fun g : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) => ψ (g • z))
    (g := e) e.injective h

def gamma0CuspHeightProfile (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (z : UpperHalfPlane) : ℂ :=
  (1/2:ℂ)*∑ᶠ v : Gamma0CuspEisensteinRows N 1 a,
    ρ (cuspEisensteinRowHeight N 1 a v z/(gamma0CuspTrueWidth N a:ℝ))

theorem gamma0CuspHeightProfile_eq_poincare (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ ⊆ Ioi (0:ℝ))
    (z : UpperHalfPlane) :
    gamma0CuspHeightProfile N a ρ z=
      (1/2:ℂ)*gamma0PoincareSeed N (cuspHeightProfileSeed N a ρ hρ hcρ hpos).val z := by
  let ψ := (cuspHeightProfileSeed N a ρ hρ hcρ hpos).val
  let e := cuspEisensteinParabolicEquiv N a
  have hg := gamma0CompactSeed_point_finite N ψ z
  have he : Function.HasFiniteSupport (fun p => ψ ((e p).val • z)) :=
    Function.HasFiniteSupport.fun_comp_of_injective
      (f := fun γ : CongruenceSubgroup.Gamma0 N => ψ (γ.val • z)) (g := e) e.injective hg
  unfold gamma0CuspHeightProfile
  congr 1
  rw [gamma0PoincareSeed_eq_finsum,← finsum_comp_equiv (f := fun γ : CongruenceSubgroup.Gamma0 N => ψ (γ.val • z)) e,
    finsum_curry _ he]
  apply finsum_congr
  intro v
  exact (cuspHeightProfileSeed_parabolic N a ρ hρ hcρ hpos v z).symm

def gamma0CuspHeightProfileEnergy (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ ⊆ Ioi (0:ℝ)) :
    gamma0EnergySpace N :=
  gamma0EnergyTest N ((1/2:ℂ) • cuspHeightProfileSeed N a ρ hρ hcρ hpos)

theorem gamma0CuspHeightProfileEnergy_mass_ae (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (ρ : ℝ → ℂ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpos : tsupport ρ ⊆ Ioi (0:ℝ))
    (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0EnergyInclusion N (gamma0CuspHeightProfileEnergy N a ρ hρ hcρ hpos) q : UpperHalfPlane → ℂ)
      =ᵐ[MeasureTheory.volume.restrict ModularGroup.fd]
      (fun z => gamma0CuspHeightProfile N a ρ (q.out⁻¹ • z)) := by
  let ψ := cuspHeightProfileSeed N a ρ hρ hcρ hpos
  have h := gamma0SeedMass_coeFn N ((1/2:ℂ) • ψ.val) q
  filter_upwards [h] with z hz
  change (gamma0SeedMass N ((1/2:ℂ) • ψ.val) q) z=_
  rw [hz,gamma0CuspHeightProfile_eq_poincare N a ρ hρ hcρ hpos]
  change arithmeticPoincareSeed (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
    ((1/2:ℂ) • ψ.val) (q.out⁻¹ • z)=_
  rw [arithmeticPoincareSeed_smul]
  rfl

end ArtinMatthews
