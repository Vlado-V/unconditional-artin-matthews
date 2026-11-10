module

public import ArtinMatthews.SpectralEisensteinOutgoingEnvelope
public import ArtinMatthews.SpectralCoreLocalizationSmoothEnergy
public import ArtinMatthews.SpectralEisensteinCutoffRegularity
public import ArtinMatthews.SpectralEisensteinGradientApproximation
public import ArtinMatthews.SpectralEisensteinRadialDerivative
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

/-! Literal outgoing mass and gradient in each ambient chart. Neither
form-domain membership nor a derivative estimate is taken as an input. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CuspOutgoingApproxEnergy (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (q : ℂ)
    (n : ℕ) : gamma0EnergySpace N :=
  gamma0CuspHeightProfileEnergy N a (eisensteinOutgoingProfile q n)
    (eisensteinOutgoingProfile_smooth q n) (eisensteinOutgoingProfile_compact q n)
    (eisensteinOutgoingProfile_positive_support q n)

theorem gamma0CuspOutgoingApproxEnergy_mass_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (n : ℕ) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0EnergyInclusion N (gamma0CuspOutgoingApproxEnergy N a q n) i : UpperHalfPlane → ℂ)
      =ᵐ[volume.restrict ModularGroup.fd]
      (fun z => gamma0CuspHeightProfile N a (eisensteinOutgoingProfile q n) (i.out⁻¹ • z)) :=
  gamma0CuspHeightProfileEnergy_mass_ae N a _ _ _ _ i

theorem gamma0CuspOutgoingApproxEnergy_gradient_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (n : ℕ) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0EnergyGradient N (gamma0CuspOutgoingApproxEnergy N a q n) i :
      UpperHalfPlane → EuclideanSpace ℂ (Fin 2))
      =ᵐ[volume.restrict ModularGroup.fd]
      (fun z => h2SectionGradient (gamma0CuspHeightProfile N a (eisensteinOutgoingProfile q n)) (i.out⁻¹ • z)) :=
  gamma0CuspHeightProfileEnergy_gradient_ae N a _ _ _ _ i

theorem gamma0CuspOutgoingCutoff_continuous (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) : Continuous (gamma0CuspEisensteinCutoff N a q) :=
  spectralSection_continuous _ (gamma0CuspEisensteinCutoff_spatial_smooth N a q)

theorem gamma0CuspOutgoingCutoff_memLp (N : ℕ) [NeZero N] (a r : SL(2,ℤ))
    (q : ℂ) (hq : q.re<1/2) :
    MemLp (fun z : UpperHalfPlane => gamma0CuspEisensteinCutoff N a q (r⁻¹ • z)) 2
      (volume.restrict ModularGroup.fd) := by
  have hc : Continuous (fun z : UpperHalfPlane => gamma0CuspEisensteinCutoff N a q (r⁻¹ • z)) := by
    change Continuous (fun z : UpperHalfPlane => gamma0CuspEisensteinCutoff N a q
      (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹ • z))
    exact (gamma0CuspOutgoingCutoff_continuous N a q).comp (continuous_const_smul _)
  exact (gamma0CuspOutgoingEnvelope_memLp N a r q hq).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => gamma0CuspOutgoingCutoff_norm_le N a q (r⁻¹ • z)))

theorem gamma0CuspOutgoingCutoff_gradient_memLp (N : ℕ) [NeZero N] (a r : SL(2,ℤ))
    (q : ℂ) (hq : q.re<1/2) :
    MemLp (fun z : UpperHalfPlane => h2SectionGradient (gamma0CuspEisensteinCutoff N a q) (r⁻¹ • z)) 2
      (volume.restrict ModularGroup.fd) := by
  obtain ⟨M,hM,hb⟩ := eisensteinHeightCutoff_weighted_deriv_bounded
  have hc : Continuous (fun z : UpperHalfPlane =>
      h2SectionGradient (gamma0CuspEisensteinCutoff N a q) (r⁻¹ • z)) := by
    change Continuous (fun z : UpperHalfPlane =>
      h2SectionGradient (gamma0CuspEisensteinCutoff N a q) (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹ • z))
    exact (h2SectionGradient_continuous _ (gamma0CuspEisensteinCutoff_spatial_smooth N a q)).comp
      (continuous_const_smul _)
  exact ((gamma0CuspOutgoingEnvelope_memLp N a r q hq).const_mul (1+M+‖q‖)).mono'
    hc.aestronglyMeasurable (Filter.Eventually.of_forall
      (fun z => gamma0CuspOutgoingCutoff_gradient_norm_le N a q hM hb (r⁻¹ • z)))

def gamma0CuspOutgoingCutoffMass (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (q : ℂ) (hq : q.re<1/2) : Gamma0RegionL2 N :=
  WithLp.toLp 2 (fun i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
    (gamma0CuspOutgoingCutoff_memLp N a i.out q hq).toLp _)

def gamma0CuspOutgoingCutoffGradientMass (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (q : ℂ) (hq : q.re<1/2) : Gamma0GradientL2 N :=
  WithLp.toLp 2 (fun i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N =>
    (gamma0CuspOutgoingCutoff_gradient_memLp N a i.out q hq).toLp _)

theorem gamma0CuspOutgoingCutoffMass_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0CuspOutgoingCutoffMass N a q hq i : UpperHalfPlane → ℂ)
      =ᵐ[volume.restrict ModularGroup.fd] (fun z => gamma0CuspEisensteinCutoff N a q (i.out⁻¹ • z)) :=
  (gamma0CuspOutgoingCutoff_memLp N a i.out q hq).coeFn_toLp

theorem gamma0CuspOutgoingCutoffGradientMass_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0CuspOutgoingCutoffGradientMass N a q hq i : UpperHalfPlane → EuclideanSpace ℂ (Fin 2))
      =ᵐ[volume.restrict ModularGroup.fd]
      (fun z => h2SectionGradient (gamma0CuspEisensteinCutoff N a q) (i.out⁻¹ • z)) :=
  (gamma0CuspOutgoingCutoff_gradient_memLp N a i.out q hq).coeFn_toLp

end ArtinMatthews
