module

public import ArtinMatthews.SpectralGamma0CuspFormGreen
public import OAI.Analysis.CoulombIonization.FormDomain.CoerciveOperator
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

/-! The actual self-adjoint mass-plus-energy operator with compact inverse
on the closed mass span of all-height mean-zero energy vectors. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

local instance cuspFormOperator_energyInner (N : ℕ) [NeZero N] : Inner ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  (gamma0AllHeightMeanZeroEnergy_innerProductSpace N).toInner
local instance cuspFormOperator_massInner (N : ℕ) [NeZero N] : Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

def gamma0AllHeightMassEnergyOperator (N : ℕ) [NeZero N] :
    gamma0AllHeightEnergyMassSpace N →ₗ.[ℂ] gamma0AllHeightEnergyMassSpace N :=
  OAI.CoulombAtom.inverseOperator (gamma0AllHeightCoreGreen N)

theorem gamma0AllHeightMassEnergyOperator_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (gamma0AllHeightMassEnergyOperator N) :=
  OAI.CoulombAtom.inverseOperator_selfAdjoint (gamma0AllHeightCoreGreen_selfAdjoint N)
    (gamma0AllHeightCoreGreen_injective N)

theorem gamma0AllHeightMassEnergyOperator_domain (N : ℕ) [NeZero N] :
    (gamma0AllHeightMassEnergyOperator N).domain = (gamma0AllHeightCoreGreen N).range :=
  OAI.CoulombAtom.inverseOperator_domain _

theorem gamma0AllHeightMassEnergyOperator_dense_domain (N : ℕ) [NeZero N] :
    Dense ((gamma0AllHeightMassEnergyOperator N).domain : Set (gamma0AllHeightEnergyMassSpace N)) :=
  (gamma0AllHeightMassEnergyOperator_selfAdjoint N).dense_domain

theorem gamma0AllHeightMassEnergyOperator_closed (N : ℕ) [NeZero N] :
    (gamma0AllHeightMassEnergyOperator N).IsClosed :=
  (gamma0AllHeightMassEnergyOperator_selfAdjoint N).isClosed

theorem gamma0AllHeightMassEnergyOperator_graph (N : ℕ) [NeZero N]
    (x y : gamma0AllHeightEnergyMassSpace N) :
    (x,y) ∈ (gamma0AllHeightMassEnergyOperator N).graph ↔ gamma0AllHeightCoreGreen N y = x :=
  OAI.CoulombAtom.inverseOperator_graph (gamma0AllHeightCoreGreen_injective N) x y

theorem gamma0AllHeightMassEnergyOperator_weak_graph (N : ℕ) [NeZero N]
    (x y : gamma0AllHeightEnergyMassSpace N) :
    (x,y) ∈ (gamma0AllHeightMassEnergyOperator N).graph ↔ ∃ u : gamma0AllHeightMeanZeroEnergy N,
      gamma0AllHeightCoreInclusion N u = x ∧ ∀ v : gamma0AllHeightMeanZeroEnergy N,
        inner ℂ u v = inner ℂ y (gamma0AllHeightCoreInclusion N v) := by
  rw [gamma0AllHeightMassEnergyOperator_graph]
  constructor
  · intro h
    exact ⟨gamma0AllHeightCoreWeakSolution N y, h, gamma0AllHeightCoreWeakSolution_equation N y⟩
  · rintro ⟨u, hu, he⟩
    change gamma0AllHeightCoreInclusion N (gamma0AllHeightCoreWeakSolution N y) = x
    rw [← gamma0AllHeightCoreWeakSolution_unique N y he, hu]

theorem gamma0AllHeightEnergy_inner (N : ℕ) [NeZero N]
    (u v : gamma0AllHeightMeanZeroEnergy N) :
    inner ℂ u v = inner ℂ (gamma0AllHeightCoreInclusion N u) (gamma0AllHeightCoreInclusion N v) +
      inner ℂ (gamma0EnergyGradient N u.val) (gamma0EnergyGradient N v.val) := rfl

theorem gamma0AllHeightMassEnergyOperator_mass_gradient_graph (N : ℕ) [NeZero N]
    (x y : gamma0AllHeightEnergyMassSpace N) :
    (x,y) ∈ (gamma0AllHeightMassEnergyOperator N).graph ↔ ∃ u : gamma0AllHeightMeanZeroEnergy N,
      gamma0AllHeightCoreInclusion N u = x ∧ ∀ v : gamma0AllHeightMeanZeroEnergy N,
        inner ℂ x (gamma0AllHeightCoreInclusion N v) +
          inner ℂ (gamma0EnergyGradient N u.val) (gamma0EnergyGradient N v.val) =
            inner ℂ y (gamma0AllHeightCoreInclusion N v) := by
  rw [gamma0AllHeightMassEnergyOperator_weak_graph]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨u, hu, fun v => ?_⟩
    rw [← hu, ← gamma0AllHeightEnergy_inner]
    exact he v
  · rintro ⟨u, hu, he⟩
    refine ⟨u, hu, fun v => ?_⟩
    rw [gamma0AllHeightEnergy_inner, hu]
    exact he v

theorem gamma0AllHeightMassEnergyOperator_lower_bound (N : ℕ) [NeZero N]
    (x y : gamma0AllHeightEnergyMassSpace N)
    (h : (x,y) ∈ (gamma0AllHeightMassEnergyOperator N).graph) :
    ‖x‖^2 ≤ (inner ℂ x y).re := by
  obtain ⟨u, hu, he⟩ := (gamma0AllHeightMassEnergyOperator_weak_graph N x y).mp h
  have hb : ‖x‖ ≤ ‖u‖ := hu ▸ gamma0AllHeightCoreInclusion_bound N u
  have hnorm : ‖u‖^2 = (inner ℂ x y).re := calc
    _ = (inner ℂ u u).re := (inner_self_eq_norm_sq (𝕜:=ℂ) u).symm
    _ = (inner ℂ y x).re := by rw [he u, hu]
    _ = _ := inner_re_symm (𝕜:=ℂ) y x
  exact ((sq_le_sq₀ (norm_nonneg x) (norm_nonneg u)).mpr hb).trans_eq hnorm

end ArtinMatthews
