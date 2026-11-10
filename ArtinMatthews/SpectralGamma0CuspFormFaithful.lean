module

public import ArtinMatthews.SpectralGamma0CuspFormOperator
public import ArtinMatthews.SpectralGamma0MassInjective
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

/-! Faithful energy representatives for the actual all-height form operator. -/
noncomputable section
namespace ArtinMatthews

local instance cuspFormFaithful_energyInner (N : ℕ) [NeZero N] : Inner ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  (gamma0AllHeightMeanZeroEnergy_innerProductSpace N).toInner
local instance cuspFormFaithful_massInner (N : ℕ) [NeZero N] : Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

theorem gamma0AllHeightCoreInclusion_injective (N : ℕ) [NeZero N] :
    Function.Injective (gamma0AllHeightCoreInclusion N) := by
  intro u v h
  exact gamma0AllHeightMassInclusion_injective N (congrArg Subtype.val h)

theorem gamma0AllHeightMassEnergyOperator_unique_energy (N : ℕ) [NeZero N]
    (x y : gamma0AllHeightEnergyMassSpace N) :
    (x,y) ∈ (gamma0AllHeightMassEnergyOperator N).graph ↔ ∃! u : gamma0AllHeightMeanZeroEnergy N,
      gamma0AllHeightCoreInclusion N u = x ∧ ∀ v : gamma0AllHeightMeanZeroEnergy N,
        inner ℂ u v = inner ℂ y (gamma0AllHeightCoreInclusion N v) := by
  constructor
  · intro h
    obtain ⟨u,hu,hweak⟩ := (gamma0AllHeightMassEnergyOperator_weak_graph N x y).mp h
    refine ⟨u,⟨hu,hweak⟩,?_⟩
    intro v hv
    exact gamma0AllHeightCoreInclusion_injective N (hv.1.trans hu.symm)
  · rintro ⟨u,hu,_⟩
    exact (gamma0AllHeightMassEnergyOperator_weak_graph N x y).mpr ⟨u,hu⟩

end ArtinMatthews
