module

public import ArtinMatthews.SpectralGamma0AmbientResolventAnalytic
public import ArtinMatthews.SpectralGamma0FormOperator
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

/-! The constructed full ambient weak resolvent is the actual resolvent
of the existing self-adjoint mass-plus-energy operator. -/
noncomputable section
namespace ArtinMatthews

theorem gamma0AmbientResolvent_operator_graph (N : ℕ) [NeZero N] (z : ℂ)
    (hz : z.re < ‖z‖) (F : Gamma0RegionL2 N) :
    (gamma0AmbientResolvent N z hz F,
      F+(z+1) • gamma0AmbientResolvent N z hz F) ∈ (gamma0MassEnergyOperator N).graph := by
  let U := gamma0AmbientWeakResolvent N z hz F
  let X := gamma0AmbientResolvent N z hz F
  have hp := gamma0AmbientWeakResolvent_pencil N z hz F
  change U-(z+1) • gamma0EnergyMassAdjoint N X=gamma0EnergyMassAdjoint N F at hp
  have he : gamma0EnergyMassAdjoint N (F+(z+1) • X)=U := by
    rw [map_add,map_smul,← hp,sub_add_cancel]
  apply (gamma0MassEnergyOperator_graph N X (F+(z+1) • X)).mpr
  change gamma0EnergyInclusion N (gamma0EnergyMassAdjoint N (F+(z+1) • X))=X
  rw [he]
  rfl

theorem gamma0AmbientResolventFamily_operator_graph (N : ℕ) [NeZero N] (z : ℂ)
    (hz : z.re < ‖z‖) (F : Gamma0RegionL2 N) :
    (gamma0AmbientResolventFamily N z F,F+(z+1) • gamma0AmbientResolventFamily N z F)
      ∈ (gamma0MassEnergyOperator N).graph := by
  rw [gamma0AmbientResolventFamily_eq N z hz]
  exact gamma0AmbientResolvent_operator_graph N z hz F

end ArtinMatthews
