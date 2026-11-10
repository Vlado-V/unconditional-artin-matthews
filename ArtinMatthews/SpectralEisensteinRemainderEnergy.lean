module

public import ArtinMatthews.SpectralEisensteinGradientApproximation
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

/-! The actual truncated Eisenstein series belongs to the genuine completed
ambient form graph, as a strong limit of explicitly constructed core vectors. -/
noncomputable section
open Set Filter Topology MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0CuspEisensteinApproxEnergy_graph_tendsto (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun n => (gamma0CuspEisensteinApproxEnergy N a s n : Gamma0EnergyAmbient N))
      atTop (𝓝 (WithLp.toLp 2 (gamma0CuspEisensteinRemainderMass N a s hs,
        gamma0CuspEisensteinRemainderGradientMass N a s hs))) := by
  have hp := (gamma0CuspEisensteinApproxEnergy_mass_tendsto N a s hs).prodMk_nhds
    (gamma0CuspEisensteinApproxEnergy_gradient_tendsto N a s hs)
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ (Gamma0RegionL2 N) (Gamma0GradientL2 N)
  have h := (e.symm.continuous.tendsto _).comp hp
  change Tendsto (fun n => e.symm (e (gamma0CuspEisensteinApproxEnergy N a s n : Gamma0EnergyAmbient N)))
    atTop (𝓝 (WithLp.toLp 2 (gamma0CuspEisensteinRemainderMass N a s hs,
      gamma0CuspEisensteinRemainderGradientMass N a s hs))) at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

theorem gamma0CuspEisensteinRemainder_mem_energyGraph (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    WithLp.toLp 2 (gamma0CuspEisensteinRemainderMass N a s hs,
      gamma0CuspEisensteinRemainderGradientMass N a s hs) ∈ gamma0EnergySpace N := by
  apply (Submodule.isClosed_topologicalClosure (gamma0EnergyGraph N).range).mem_of_tendsto
    (gamma0CuspEisensteinApproxEnergy_graph_tendsto N a s hs)
  exact Filter.Eventually.of_forall (fun n => (gamma0CuspEisensteinApproxEnergy N a s n).property)

def gamma0CuspEisensteinRemainderEnergy (N : ℕ) [NeZero N] (a : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) : gamma0EnergySpace N :=
  ⟨WithLp.toLp 2 (gamma0CuspEisensteinRemainderMass N a s hs,
    gamma0CuspEisensteinRemainderGradientMass N a s hs),
    gamma0CuspEisensteinRemainder_mem_energyGraph N a s hs⟩

theorem gamma0CuspEisensteinRemainderEnergy_mass (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    gamma0EnergyInclusion N (gamma0CuspEisensteinRemainderEnergy N a s hs)=
      gamma0CuspEisensteinRemainderMass N a s hs := rfl

theorem gamma0CuspEisensteinRemainderEnergy_gradient (N : ℕ) [NeZero N]
    (a : SL(2,ℤ)) (s : ℂ) (hs : 1 < s.re) :
    gamma0EnergyGradient N (gamma0CuspEisensteinRemainderEnergy N a s hs)=
      gamma0CuspEisensteinRemainderGradientMass N a s hs := rfl

end ArtinMatthews
