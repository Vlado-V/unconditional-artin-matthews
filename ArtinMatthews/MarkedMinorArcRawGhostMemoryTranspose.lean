module

public import ArtinMatthews.MarkedMinorArcRawGhostChargeNormalForm
public import ArtinMatthews.MarkedMinorArcRawGhostTotalDegreeAdjoint
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

/-! Genuine factorial transpose of the original finite indexed memory
rule, with both actual total-memory cutoffs retained.  The identity is
derived from the literal choice normal form and the grouped deletion/birth
integration, not supplied as an adjoint or distribution hypothesis. -/
namespace ArtinMatthews
open scoped BigOperators

theorem markedRawGhostMemoryRule_transpose {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ s : J → ℝ)
    {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (f g : MarkedRawMemory P B → ℂ)
    (hf : MarkedRawMemorySymmetric f) (hg : MarkedRawMemorySymmetric g) :
    (∑ m : MarkedRawMemory P B,(markedRawMemoryMass ν m : ℂ)*g m*
      markedRawGhostMemoryRule ν δ γ s z hz f m)=
      ∑ m : MarkedRawMemory P B,(markedRawMemoryMass ν m : ℂ)*f m*
        markedRawGhostMemoryRule ν γ δ s z hz g m := by
  rw [markedRawGhostMemoryRule_degree_normalForm,
    markedRawGhostMemoryRule_degree_normalForm]
  simp only [markedRawGhostDegreeSourceFactor]
  exact markedRawGhost_total_degree_transpose P (fun j p => (ν j p : ℂ)) z hz B
    (fun j => (δ j : ℂ)) (fun j => (γ j : ℂ)) (fun j => (s j : ℂ))
    (fun k hk a => g (markedRawMemoryOfDegrees P k hk a))
    (fun k hk a => f (markedRawMemoryOfDegrees P k hk a))
    (markedRawMemory_symmetric_degree_family g hg)
    (markedRawMemory_symmetric_degree_family f hf)

end ArtinMatthews
