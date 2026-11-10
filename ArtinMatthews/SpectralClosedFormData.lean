module

public import ArtinMatthews.SpectralClosedSubspaceResolvent
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Package the actual closed form data before specializing its resolvent.
The package keeps the inherited Hilbert structures fixed throughout the
proof and avoids reconstructing a nested subtype at each operator theorem. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

structure SpectralClosedFormData (V H : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  subspace : Submodule ℂ V
  closed : IsClosed (subspace:Set V)
  inclusion : V →L[ℂ] H
  compact : IsCompactOperator (spectralClosedFormInclusion subspace inclusion)
  injective : Function.Injective inclusion
  bound : ∀ u : subspace, ‖inclusion u.val‖≤‖u‖

namespace SpectralClosedFormData
section
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def exceptional (d : SpectralClosedFormData V H) : Set ℂ :=
  spectralClosedFormExceptional d.subspace d.closed d.inclusion

def resolvent (d : SpectralClosedFormData V H) : ℂ → H →L[ℂ] H :=
  spectralClosedFormResolvent d.subspace d.closed d.inclusion

theorem exceptional_finite_norm_le (d : SpectralClosedFormData V H) (R : ℝ) (hR : 0≤R) :
    {z : ℂ | z∈d.exceptional ∧ ‖z‖≤R}.Finite :=
  spectralClosedFormExceptional_finite_norm_le d.subspace d.closed d.inclusion d.compact R hR

theorem exceptional_nonnegative (d : SpectralClosedFormData V H) (z : ℂ) (hz : z∈d.exceptional) :
    ∃ r : ℝ, 0≤r ∧ z=(r:ℂ) :=
  spectralClosedFormExceptional_nonnegative d.subspace d.closed d.inclusion d.injective d.bound z hz

theorem resolvent_meromorphic (d : SpectralClosedFormData V H) : Meromorphic d.resolvent :=
  spectralClosedFormResolvent_meromorphic d.subspace d.closed d.inclusion d.compact

theorem resolvent_weak (d : SpectralClosedFormData V H) (z : ℂ) (hz : z∉d.exceptional) (F : H) :
    ∃ u : V, u∈d.subspace ∧ d.inclusion u=d.resolvent z F ∧
      ∀ v : V, v∈d.subspace → inner ℂ v u-(z+1)*inner ℂ (d.inclusion v) (d.inclusion u)=
        inner ℂ (d.inclusion v) F := by
  let u := spectralClosedFormWeakResolvent d.subspace d.closed d.inclusion z F
  refine ⟨u.val,u.property,rfl,?_⟩
  intro v hv
  exact spectralClosedFormWeakResolvent_equation d.subspace d.closed d.inclusion d.compact z hz F ⟨v,hv⟩

end
end SpectralClosedFormData
end ArtinMatthews
