module

public import ArtinMatthews.SpectralClosedFormData
public import ArtinMatthews.SpectralGamma0MassInjective
public import ArtinMatthews.SpectralGamma0TruncatedMeanZero
public import ArtinMatthews.SpectralGamma0FormOperator
public import ArtinMatthews.SpectralGamma0TruncatedCompact
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

/-! The actual meromorphic pseudo-resolvent of the truncated constant-mode
energy form. Its weak equations are restricted only in the test domain;
they do not assert replacement of the full ambient Laplacian. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

def gamma0TruncatedFormData (N : ℕ) [NeZero N] (A : ℝ) (hA : 0<A) :
    SpectralClosedFormData (gamma0EnergySpace N) (Gamma0RegionL2 N) where
  subspace := gamma0TruncatedMeanZeroEnergy N A hA
  closed := gamma0TruncatedMeanZeroEnergy_isClosed N A hA
  inclusion := gamma0EnergyInclusion N
  compact := by
    change IsCompactOperator (gamma0TruncatedMassInclusion N A hA)
    exact gamma0TruncatedMassInclusion_compact N A hA
  injective := gamma0EnergyInclusion_injective N
  bound u := gamma0EnergyInclusion_bound N u.val

def gamma0TruncatedPseudoExceptional (N : ℕ) [NeZero N] (A : ℝ) (hA : 0<A) : Set ℂ :=
  (gamma0TruncatedFormData N A hA).exceptional

def gamma0TruncatedPseudoResolvent (N : ℕ) [NeZero N] (A : ℝ) (hA : 0<A) :
    ℂ → Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  (gamma0TruncatedFormData N A hA).resolvent

theorem gamma0TruncatedPseudoExceptional_finite_norm_le (N : ℕ) [NeZero N]
    (A : ℝ) (hA : 0<A) (R : ℝ) (hR : 0≤R) :
    {z : ℂ | z∈gamma0TruncatedPseudoExceptional N A hA ∧ ‖z‖≤R}.Finite :=
  (gamma0TruncatedFormData N A hA).exceptional_finite_norm_le R hR

theorem gamma0TruncatedPseudoExceptional_nonnegative (N : ℕ) [NeZero N]
    (A : ℝ) (hA : 0<A) (z : ℂ) (hz : z∈gamma0TruncatedPseudoExceptional N A hA) :
    ∃ r : ℝ, 0≤r ∧ z=(r:ℂ) :=
  (gamma0TruncatedFormData N A hA).exceptional_nonnegative z hz

theorem gamma0TruncatedPseudoResolvent_meromorphic (N : ℕ) [NeZero N]
    (A : ℝ) (hA : 0<A) : Meromorphic (gamma0TruncatedPseudoResolvent N A hA) :=
  (gamma0TruncatedFormData N A hA).resolvent_meromorphic

theorem gamma0TruncatedPseudoResolvent_weak (N : ℕ) [NeZero N]
    (A : ℝ) (hA : 0<A) (z : ℂ) (hz : z∉gamma0TruncatedPseudoExceptional N A hA)
    (F : Gamma0RegionL2 N) :
    ∃ u : gamma0EnergySpace N, u∈gamma0TruncatedMeanZeroEnergy N A hA ∧
      gamma0EnergyInclusion N u=gamma0TruncatedPseudoResolvent N A hA z F ∧
      ∀ v : gamma0EnergySpace N, v∈gamma0TruncatedMeanZeroEnergy N A hA →
        inner ℂ (gamma0EnergyGradient N v) (gamma0EnergyGradient N u)-
          z*inner ℂ (gamma0EnergyInclusion N v) (gamma0EnergyInclusion N u)=
        inner ℂ (gamma0EnergyInclusion N v) F := by
  obtain ⟨u,hu,hm,hweak⟩ := (gamma0TruncatedFormData N A hA).resolvent_weak z hz F
  refine ⟨u,hu,hm,?_⟩
  intro v hv
  have he := hweak v hv
  change inner ℂ v u-(z+1)*inner ℂ (gamma0EnergyInclusion N v) (gamma0EnergyInclusion N u)=
    inner ℂ (gamma0EnergyInclusion N v) F at he
  rw [gamma0FormEnergy_inner] at he
  linear_combination he

end ArtinMatthews
