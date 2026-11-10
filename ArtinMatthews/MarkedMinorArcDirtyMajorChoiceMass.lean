module

public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceFiber
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFixedFactors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! Exact prime integration and finite partition into the genuine major
choice fibers. These keep the actual old index multiplicities. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedDirtyMajorChoiceFiber_prime_mass {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) (store : J → Bool)
    (indices : MarkedRawPromotionTuple s.2.2 I) (fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1))
    (choice : MarkedDirtyFixedEdgeChoice hZ s I)
    (hc : choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh) :
    markedRawEdgeChoicePrimeMass ν V hZ s choice.1=
      finiteProductMass (fun j : ↥(Finset.univ \ I) => ν j.1) fresh*(∏ j ∈ I, (V j)⁻¹) := by
  have hf := congrArg (fun labels => labels.2.2) (Finset.mem_filter.mp hc).2
  rw [markedDirtyFixedEdgeChoice_prime_mass,hf]

theorem markedDirtyMajorChoice_fiberwise_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (f : MarkedDirtyFixedEdgeChoice hZ s I → ℝ) :
    (∑ choice : MarkedDirtyFixedEdgeChoice hZ s I, f choice)=
      ∑ store : J → Bool, ∑ indices : MarkedRawPromotionTuple s.2.2 I,
        ∑ fresh : (j : ↥(Finset.univ \ I)) → ↥(P j.1),
          ∑ choice ∈ markedDirtyMajorChoiceFiber hZ s I store indices fresh, f choice := by
  classical
  have hh := Finset.sum_fiberwise (Finset.univ : Finset (MarkedDirtyFixedEdgeChoice hZ s I))
    (fun choice => (markedDirtyFixedEdgeChoiceCode hZ s I choice).2) f
  simpa only [Fintype.sum_prod_type,markedDirtyMajorChoiceFiber] using hh.symm

end ArtinMatthews
