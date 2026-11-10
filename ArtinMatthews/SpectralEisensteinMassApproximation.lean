module

public import ArtinMatthews.SpectralEisensteinEnvelopeL2
public import ArtinMatthews.SpectralEisensteinRemainderL2
public import ArtinMatthews.SpectralEisensteinRemainderSeries
public import ArtinMatthews.SpectralL2DominatedConvergence
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

/-! Actual compact-core energy vectors whose mass coordinates converge
strongly to the genuine truncated Eisenstein mass. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CuspEisensteinApproxEnergy (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (s : ℂ)
    (n : ℕ) : gamma0EnergySpace N :=
  gamma0CuspHeightProfileEnergy N a (eisensteinRadialApprox s (n+1:ℕ))
    (eisensteinRadialApprox_smooth s (by positivity))
    (eisensteinRadialApprox_compact s (by positivity))
    (eisensteinRadialApprox_positive_support s (by positivity))

theorem gamma0CuspEisensteinApproxEnergy_mass_ae (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (n : ℕ) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    (gamma0EnergyInclusion N (gamma0CuspEisensteinApproxEnergy N a s n) q : UpperHalfPlane → ℂ)
      =ᵐ[volume.restrict ModularGroup.fd]
      (fun z => gamma0CuspHeightProfile N a (eisensteinRadialApprox s (n+1:ℕ)) (q.out⁻¹ • z)) :=
  gamma0CuspHeightProfileEnergy_mass_ae N a _ _ _ _ q

theorem gamma0CuspEisensteinRemainder_norm_envelope (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    ‖gamma0CuspEisensteinRemainder N a s z‖ ≤ gamma0CuspRadialEnvelope N a s.re z :=
  le_of_tendsto (gamma0CuspEisensteinRadialApprox_tendsto N a s hs z).norm
    (Filter.Eventually.of_forall (fun n => gamma0CuspRadialApprox_norm_le N a s hs
      (by positivity : (0:ℝ)<(n+1:ℕ)) z))

theorem gamma0CuspEisensteinApproxEnergy_mass_chart_tendsto (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) (q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    Tendsto (fun n => gamma0EnergyInclusion N (gamma0CuspEisensteinApproxEnergy N a s n) q)
      atTop (𝓝 (gamma0CuspEisensteinRemainderMass N a s hs q)) := by
  let u (n : ℕ) (z : UpperHalfPlane) :=
    gamma0CuspHeightProfile N a (eisensteinRadialApprox s (n+1:ℕ)) (q.out⁻¹ • z)
  let v (z : UpperHalfPlane) := gamma0CuspEisensteinRemainder N a s (q.out⁻¹ • z)
  have hu (n : ℕ) : MemLp (u n) 2 (volume.restrict ModularGroup.fd) :=
    gamma0CuspCompactProfile_memLp N a q.out _ (eisensteinRadialApprox_smooth s (by positivity))
      (eisensteinRadialApprox_compact s (by positivity))
      (eisensteinRadialApprox_positive_support s (by positivity))
  have hv : MemLp v 2 (volume.restrict ModularGroup.fd) :=
    gamma0CuspEisensteinRemainder_memLp_modularRegion N a s hs q.out
  have h := spectralL2_toLp_dominated_convergence u v hu hv
    (fun z => gamma0CuspRadialEnvelope N a s.re (q.out⁻¹ • z))
    (gamma0CuspRadialEnvelope_memLp N a q.out s.re hs)
    (fun n => Filter.Eventually.of_forall (fun z => gamma0CuspRadialApprox_norm_le N a s hs
      (by positivity : (0:ℝ)<(n+1:ℕ)) _))
    (Filter.Eventually.of_forall (fun z => gamma0CuspEisensteinRemainder_norm_envelope N a s hs _))
    (Filter.Eventually.of_forall (fun z => gamma0CuspEisensteinRadialApprox_tendsto N a s hs _))
  have he (n : ℕ) : (hu n).toLp (u n)=
      gamma0EnergyInclusion N (gamma0CuspEisensteinApproxEnergy N a s n) q := by
    apply Lp.ext
    exact (hu n).coeFn_toLp.trans (gamma0CuspEisensteinApproxEnergy_mass_ae N a s n q).symm
  have he' : hv.toLp v=gamma0CuspEisensteinRemainderMass N a s hs q := by
    apply Lp.ext
    exact hv.coeFn_toLp.trans (gamma0CuspEisensteinRemainderMass_ae N a s hs q).symm
  simpa only [he,he'] using h

theorem gamma0CuspEisensteinApproxEnergy_mass_tendsto (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun n => gamma0EnergyInclusion N (gamma0CuspEisensteinApproxEnergy N a s n))
      atTop (𝓝 (gamma0CuspEisensteinRemainderMass N a s hs)) := by
  have h : Tendsto (fun n => fun q =>
      gamma0EnergyInclusion N (gamma0CuspEisensteinApproxEnergy N a s n) q) atTop
      (𝓝 (fun q => gamma0CuspEisensteinRemainderMass N a s hs q)) := by
    apply tendsto_pi_nhds.mpr
    intro q
    exact gamma0CuspEisensteinApproxEnergy_mass_chart_tendsto N a s hs q
  simpa only [Function.comp_def,WithLp.toLp_ofLp] using
    (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp h

end ArtinMatthews
