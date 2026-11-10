module

public import ArtinMatthews.SpectralEisensteinOutgoingCharts
public import ArtinMatthews.SpectralEisensteinGradientApproximation
public import ArtinMatthews.SpectralEisensteinOutgoingGerms
public import ArtinMatthews.SpectralEisensteinRadialDerivative
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

/-! Actual full ambient form membership of the outgoing cutoff is obtained
by strong convergence in both mass and gradient of compact-core vectors. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspOutgoingApproxEnergy_mass_chart_tendsto (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    Tendsto (fun n => gamma0EnergyInclusion N (gamma0CuspOutgoingApproxEnergy N a q n) i)
      atTop (𝓝 (gamma0CuspOutgoingCutoffMass N a q hq i)) := by
  let u (n : ℕ) (z : UpperHalfPlane) := gamma0CuspHeightProfile N a (eisensteinOutgoingProfile q n) (i.out⁻¹ • z)
  let v (z : UpperHalfPlane) := gamma0CuspEisensteinCutoff N a q (i.out⁻¹ • z)
  have hu (n : ℕ) : MemLp (u n) 2 (volume.restrict ModularGroup.fd) :=
    gamma0CuspCompactProfile_memLp N a i.out _ (eisensteinOutgoingProfile_smooth q n)
      (eisensteinOutgoingProfile_compact q n) (eisensteinOutgoingProfile_positive_support q n)
  have hv : MemLp v 2 (volume.restrict ModularGroup.fd) :=
    gamma0CuspOutgoingCutoff_memLp N a i.out q hq
  have ht : ∀ z : UpperHalfPlane, Tendsto (fun n => u n z) atTop (𝓝 (v z)) := by
    intro z
    apply tendsto_const_nhds.congr'
    filter_upwards [gamma0CuspOutgoingApprox_eventually_value N a q (i.out⁻¹ • z)] with n hn
    exact hn.symm
  have h := spectralL2_toLp_dominated_convergence u v hu hv
    (fun z => gamma0CuspOutgoingEnvelope N a q (i.out⁻¹ • z))
    (gamma0CuspOutgoingEnvelope_memLp N a i.out q hq)
    (fun n => Filter.Eventually.of_forall (fun z => gamma0CuspOutgoingApprox_norm_le N a q n (i.out⁻¹ • z)))
    (Filter.Eventually.of_forall (fun z => gamma0CuspOutgoingCutoff_norm_le N a q (i.out⁻¹ • z)))
    (Filter.Eventually.of_forall ht)
  have he (n : ℕ) : (hu n).toLp (u n)=gamma0EnergyInclusion N (gamma0CuspOutgoingApproxEnergy N a q n) i :=
    Lp.ext ((hu n).coeFn_toLp.trans (gamma0CuspOutgoingApproxEnergy_mass_ae N a q n i).symm)
  have he' : hv.toLp v=gamma0CuspOutgoingCutoffMass N a q hq i :=
    Lp.ext (hv.coeFn_toLp.trans (gamma0CuspOutgoingCutoffMass_ae N a q hq i).symm)
  simpa only [he,he'] using h

theorem gamma0CuspOutgoingApproxEnergy_gradient_chart_tendsto (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (i : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :
    Tendsto (fun n => gamma0EnergyGradient N (gamma0CuspOutgoingApproxEnergy N a q n) i)
      atTop (𝓝 (gamma0CuspOutgoingCutoffGradientMass N a q hq i)) := by
  obtain ⟨M,hM,hb⟩ := eisensteinHeightCutoff_weighted_deriv_bounded
  let u (n : ℕ) (z : UpperHalfPlane) :=
    h2SectionGradient (gamma0CuspHeightProfile N a (eisensteinOutgoingProfile q n)) (i.out⁻¹ • z)
  let v (z : UpperHalfPlane) := h2SectionGradient (gamma0CuspEisensteinCutoff N a q) (i.out⁻¹ • z)
  have hu (n : ℕ) : MemLp (u n) 2 (volume.restrict ModularGroup.fd) :=
    gamma0CuspCompactProfile_gradient_memLp N a _ (eisensteinOutgoingProfile_smooth q n)
      (eisensteinOutgoingProfile_compact q n) (eisensteinOutgoingProfile_positive_support q n) i
  have hv : MemLp v 2 (volume.restrict ModularGroup.fd) :=
    gamma0CuspOutgoingCutoff_gradient_memLp N a i.out q hq
  have ht : ∀ z : UpperHalfPlane, Tendsto (fun n => u n z) atTop (𝓝 (v z)) := by
    intro z
    apply tendsto_const_nhds.congr'
    filter_upwards [gamma0CuspOutgoingApprox_eventually_gradient N a q (i.out⁻¹ • z)] with n hn
    exact hn.symm
  have h := spectralL2_toLp_dominated_convergence u v hu hv
    (fun z => (1+M+‖q‖)*gamma0CuspOutgoingEnvelope N a q (i.out⁻¹ • z))
    ((gamma0CuspOutgoingEnvelope_memLp N a i.out q hq).const_mul (1+M+‖q‖))
    (fun n => Filter.Eventually.of_forall
      (fun z => gamma0CuspOutgoingApprox_gradient_norm_le N a q n hM hb (i.out⁻¹ • z)))
    (Filter.Eventually.of_forall
      (fun z => gamma0CuspOutgoingCutoff_gradient_norm_le N a q hM hb (i.out⁻¹ • z)))
    (Filter.Eventually.of_forall ht)
  have he (n : ℕ) : (hu n).toLp (u n)=gamma0EnergyGradient N (gamma0CuspOutgoingApproxEnergy N a q n) i :=
    Lp.ext ((hu n).coeFn_toLp.trans (gamma0CuspOutgoingApproxEnergy_gradient_ae N a q n i).symm)
  have he' : hv.toLp v=gamma0CuspOutgoingCutoffGradientMass N a q hq i :=
    Lp.ext (hv.coeFn_toLp.trans (gamma0CuspOutgoingCutoffGradientMass_ae N a q hq i).symm)
  simpa only [he,he'] using h

theorem gamma0CuspOutgoingApproxEnergy_graph_tendsto (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) :
    Tendsto (fun n => (gamma0CuspOutgoingApproxEnergy N a q n : Gamma0EnergyAmbient N))
      atTop (𝓝 (WithLp.toLp 2 (gamma0CuspOutgoingCutoffMass N a q hq,
        gamma0CuspOutgoingCutoffGradientMass N a q hq))) := by
  have hm : Tendsto (fun n => gamma0EnergyInclusion N (gamma0CuspOutgoingApproxEnergy N a q n))
      atTop (𝓝 (gamma0CuspOutgoingCutoffMass N a q hq)) := by
    have h := tendsto_pi_nhds.mpr (gamma0CuspOutgoingApproxEnergy_mass_chart_tendsto N a q hq)
    simpa only [Function.comp_def,WithLp.toLp_ofLp] using
      (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp h
  have hg : Tendsto (fun n => gamma0EnergyGradient N (gamma0CuspOutgoingApproxEnergy N a q n))
      atTop (𝓝 (gamma0CuspOutgoingCutoffGradientMass N a q hq)) := by
    have h := tendsto_pi_nhds.mpr (gamma0CuspOutgoingApproxEnergy_gradient_chart_tendsto N a q hq)
    simpa only [Function.comp_def,WithLp.toLp_ofLp] using
      (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp h
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ (Gamma0RegionL2 N) (Gamma0GradientL2 N)
  have h := (e.symm.continuous.tendsto _).comp (hm.prodMk_nhds hg)
  change Tendsto (fun n => e.symm (e (gamma0CuspOutgoingApproxEnergy N a q n : Gamma0EnergyAmbient N)))
    atTop (𝓝 (WithLp.toLp 2 (gamma0CuspOutgoingCutoffMass N a q hq,
      gamma0CuspOutgoingCutoffGradientMass N a q hq))) at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

theorem gamma0CuspOutgoingCutoff_mem_energyGraph (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) :
    WithLp.toLp 2 (gamma0CuspOutgoingCutoffMass N a q hq,
      gamma0CuspOutgoingCutoffGradientMass N a q hq) ∈ gamma0EnergySpace N := by
  apply (Submodule.isClosed_topologicalClosure (gamma0EnergyGraph N).range).mem_of_tendsto
    (gamma0CuspOutgoingApproxEnergy_graph_tendsto N a q hq)
  exact Filter.Eventually.of_forall (fun n => (gamma0CuspOutgoingApproxEnergy N a q n).property)

def gamma0CuspOutgoingCutoffEnergy (N : ℕ) [NeZero N] (a : SL(2,ℤ)) (q : ℂ)
    (hq : q.re<1/2) : gamma0EnergySpace N :=
  ⟨WithLp.toLp 2 (gamma0CuspOutgoingCutoffMass N a q hq,
    gamma0CuspOutgoingCutoffGradientMass N a q hq),gamma0CuspOutgoingCutoff_mem_energyGraph N a q hq⟩

theorem gamma0CuspOutgoingCutoffEnergy_mass (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) :
    gamma0EnergyInclusion N (gamma0CuspOutgoingCutoffEnergy N a q hq)=
      gamma0CuspOutgoingCutoffMass N a q hq := rfl

theorem gamma0CuspOutgoingCutoffEnergy_gradient (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) :
    gamma0EnergyGradient N (gamma0CuspOutgoingCutoffEnergy N a q hq)=
      gamma0CuspOutgoingCutoffGradientMass N a q hq := rfl

end ArtinMatthews
