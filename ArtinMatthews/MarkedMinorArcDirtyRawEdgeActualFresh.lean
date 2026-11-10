module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFreshInteger
public import ArtinMatthews.MarkedMinorArcDirtyFreshGood
public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import ArtinMatthews.MarkedMinorArcBanRawCollision
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

/-! Exact actual-band fresh-law transport in the edge row, preserving the
literal integer product and the unnormalized tilted measure. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedDirtyActualFresh_expectation_eq {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (q x : ℝ) (f : ℤ → ℝ) :
    (∑ fresh : (j : J) → ↥(markedRawActualPrimeBand e x j),
      finiteProductMass (markedRawActualPrimeAtom e q x) fresh*
        f (markedDirtyRawFreshIntegerProduct fresh)) =
      ∑ fresh : MarkedFreshPrimeTuple e x,
        markedFreshTiltedLaw e q x fresh*f (markedFreshIntegerProduct e x fresh) := by
  classical
  rw [← Equiv.sum_comp (markedBanRawLastEquiv e x) (fun fresh =>
    markedFreshTiltedLaw e q x fresh*f (markedFreshIntegerProduct e x fresh))]
  apply Finset.sum_congr rfl
  intro fresh _
  have hm := markedBanRawLastMass_eq e q x fresh
  have hp := markedBanRawLastProduct_eq e x fresh
  rw [markedDirtyRawFreshIntegerProduct_eq,hp]
  exact congrArg (fun c => c*f (markedFreshIntegerProduct e x (markedBanRawLastEquiv e x fresh))) hm

end ArtinMatthews
