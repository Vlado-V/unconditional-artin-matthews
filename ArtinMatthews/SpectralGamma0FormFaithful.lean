module

public import ArtinMatthews.SpectralGamma0FormOperator
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

/-! Faithfulness of the actual completed energy representation: the weak
derivative closability theorem makes each mass representative unique. -/
noncomputable section
namespace ArtinMatthews

theorem gamma0MassEnergyOperator_unique_energy (N : ℕ) [NeZero N]
    (x y : Gamma0RegionL2 N) :
    (x,y) ∈ (gamma0MassEnergyOperator N).graph ↔ ∃! u : gamma0EnergySpace N,
      gamma0EnergyInclusion N u = x ∧ ∀ v : gamma0EnergySpace N,
        inner ℂ u v = inner ℂ y (gamma0EnergyInclusion N v) := by
  constructor
  · intro h
    obtain ⟨u,hu,hweak⟩ := (gamma0MassEnergyOperator_weak_graph N x y).mp h
    refine ⟨u,⟨hu,hweak⟩,?_⟩
    intro v hv
    exact gamma0EnergyInclusion_injective N (hv.1.trans hu.symm)
  · rintro ⟨u,hu,_⟩
    exact (gamma0MassEnergyOperator_weak_graph N x y).mpr ⟨u,hu⟩

end ArtinMatthews
