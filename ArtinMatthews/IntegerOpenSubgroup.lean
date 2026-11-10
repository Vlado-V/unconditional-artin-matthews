module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The compact open additive subgroup of valuation integers and its actual
surjective residue reduction. -/

namespace ArtinMatthews.QuadraticWeil

open scoped ValuativeRel Classical

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

def integerOpenSubgroup : OpenAddSubgroup K where
  toAddSubgroup := (ValuativeRel.valuation K).integer.toAddSubgroup
  isOpen' := by
    apply AddSubgroup.isOpen_of_mem_nhds
    apply (IsValuativeTopology.mem_nhds_zero_iff _).mpr
    refine ⟨1, ?_⟩
    intro x hx
    change ValuativeRel.valuation K x < 1 at hx
    exact hx.le

theorem integerOpenSubgroup_compact : IsCompact (integerOpenSubgroup K : Set K) :=
  IsNonarchimedeanLocalField.isCompact_closedBall K 1

def integerReduction : integerOpenSubgroup K →+ 𝓀[K] := by
  change 𝒪[K] →+ 𝓀[K]
  exact (IsLocalRing.residue 𝒪[K]).toAddMonoidHom

theorem integerReduction_apply (x : integerOpenSubgroup K) :
    integerReduction K x = IsLocalRing.residue 𝒪[K] ⟨(x : K), x.property⟩ := rfl

theorem integerReduction_surjective : Function.Surjective (integerReduction K) := by
  intro z
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨⟨(x : K), x.property⟩, hx⟩

end

end ArtinMatthews.QuadraticWeil
