module

public import ArtinMatthews.GiantCandidatePrimeResidueModel
public import ArtinMatthews.GiantCandidateActualResidueMask
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

/-! Product-dyad transfer for arbitrary separate residue tests at a
bounded number of the actual candidate primes. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators

theorem giant_candidate_actual_prime_mask_eventually (τ A : ℝ)
    (hτ : 0 < τ) (hA : 0 ≤ A) (r j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ U : Finset ℕ,U ⊆ giantCandidateFullPrimes x → U.card≤r →
      ∀ (H : Fin j → ℕ) (E : ∀ p : U,Finset (Fin j → ZMod p.val)),(∀ i,x^τ≤(H i:ℝ)) →
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      let S (i : Fin j) := giantCandidateRoughFullDyad W (H i)
      let ε := (Real.log x)^(-A)
      let μ := ((giantCandidatePrimeTupleMask S E).card:ℝ)/((Fintype.piFinset S).card:ℝ)
      let v := ∏ p : U,((E p).card:ℝ)/(p.val:ℝ)^j
      0 < (Fintype.piFinset S).card ∧ (1-ε)^j*v ≤ μ ∧ μ ≤ (1+ε)^j*v := by
  filter_upwards [giantCandidateFullPrimes_prime_upper_eventually,
    giant_candidate_actual_rough_residue_mask_eventually τ A hτ hA r j] with x hP hmask
  intro U hU hr H E hH
  have hprime : ∀p∈U,p.Prime := fun p hp => (hP p (hU hp)).1
  have h := hmask U hU hr H (giantCandidatePrimeCRTMask U hprime E) hH
  simpa only [giantCandidatePrimeCRTMask_uniformMass,giantCandidateTupleResidueMass,
    ← giantCandidatePrimeTupleMask_eq_residueMask U hprime] using h

end
end ArtinMatthews
