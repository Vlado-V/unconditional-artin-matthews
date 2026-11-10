module

public import ArtinMatthews.GiantFullPrimeMean
public import ArtinMatthews.GiantResidueLifespanChoice
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Finite summation over the actual family of prime lifespans,
including the common baseline normalization. -/

namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev GiantSignedFullPrimeLifespanChoice {J : Type*} [Fintype J] {PB : J → Finset ℕ}
    {M n : ℕ} (labels : Fin (n + 1) → MarkedPhysicalMarking PB M) :=
  (p : ↥(markedPhysicalBandPrimes PB)) →
    GiantSignedResidueLifespanChoice (giantSignedActualActiveVisits labels p.val)

/-- The actual full-prime average is the finite sum of products of literal
single-prime lifespan weights. -/
theorem giantSignedFullPrimeResidueMean_lifespans {J : Type*} [Fintype J]
    {PB : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val] {M n : ℕ}
    (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ) :
    giantSignedFullPrimeResidueMean labels offset q =
      ∑ c : GiantSignedFullPrimeLifespanChoice labels,
        ∏ p : ↥(markedPhysicalBandPrimes PB),
          giantSignedResidueLifespanWeight p.val offset q (giantSignedActualActiveVisits labels p.val) (c p) := by
  rw [giantSignedFullPrimeResidueMean_product]
  simp_rw [giantSignedPrimeResidueExpectation_choice_sum]
  exact Fintype.prod_sum _

/-- The common baseline factors out exactly across every numeric prime. -/
theorem giantSignedFullPrimeResidueMean_baselines {J : Type*} [Fintype J]
    {PB : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes PB), NeZero p.val] {M n : ℕ}
    (labels : Fin (n + 1) → MarkedPhysicalMarking PB M)
    (offset : Fin (n + 1) → ℤ) (q : Fin (n + 1) → ℝ)
    (hb : ∀ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeResidueBaseline p.val q ≠ 0) :
    giantSignedFullPrimeResidueMean labels offset q =
      (∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeResidueBaseline p.val q) *
        ∑ c : GiantSignedFullPrimeLifespanChoice labels,
          ∏ p : ↥(markedPhysicalBandPrimes PB),
            giantSignedResidueLifespanWeight p.val offset q (giantSignedActualActiveVisits labels p.val) (c p) /
              giantSignedPrimeResidueBaseline p.val q := by
  rw [giantSignedFullPrimeResidueMean_lifespans]
  simp_rw [Finset.prod_div_distrib]
  rw [← Finset.sum_div]
  have hprod : (∏ p : ↥(markedPhysicalBandPrimes PB), giantSignedPrimeResidueBaseline p.val q) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => hb p)
  field_simp

end
end ArtinMatthews
