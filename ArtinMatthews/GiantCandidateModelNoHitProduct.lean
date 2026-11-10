module

public import ArtinMatthews.GiantCandidateModelHitCoordinates
public import Mathlib.Analysis.Complex.Exponential
public import ArtinMatthews.GiantCandidatePrimeHitLower
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

/-! All the no-hit atoms in one group retain a uniformly positive
product once the candidate primes are large. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateModelHitAtom_nonneg {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) (p : giantCandidateSelectionPrimes G)
    (side : GiantCandidateHitSide) :
    0≤giantCandidateModelHitAtom G hG j p side := by
  unfold giantCandidateModelHitAtom
  positivity

theorem giantCandidateModelHitAtom_le {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) {j : ℕ} (hj : 0<j) (p : giantCandidateSelectionPrimes G)
    (side : GiantCandidateHitSide) :
    giantCandidateModelHitAtom G hG j p side≤(j:ℝ)/(p.val:ℝ) := by
  let _ : Fact p.val.Prime := ⟨giantCandidateModelPrime_prime G hG p⟩
  rw [giantCandidateModelHitAtom_eq]
  exact giantCandidatePrimeHitProbability_le p.val j hj side

theorem giantCandidateModelNoHitProduct_ge {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) {j : ℕ} (hj : 0<j)
    (hlarge : ∀p : giantCandidateSelectionPrimes G,4*(j:ℝ)≤(p.val:ℝ))
    (hmass : (∑ p : giantCandidateSelectionPrimes G,1/(p.val:ℝ))≤1) :
    Real.exp (-(4*(j:ℝ)))≤∏ p : giantCandidateSelectionPrimes G,giantCandidateModelNoHitAtom G hG j p := by
  let U := giantCandidateSelectionPrimes G
  let u (p : U) := giantCandidateModelHitAtom G hG j p .predecessor+
    giantCandidateModelHitAtom G hG j p .product
  have hu₀ (p : U) : 0≤u p :=
    add_nonneg (giantCandidateModelHitAtom_nonneg G hG j p _) (giantCandidateModelHitAtom_nonneg G hG j p _)
  have hu (p : U) : u p≤(2*(j:ℝ))/(p.val:ℝ) := by
    have h := add_le_add (giantCandidateModelHitAtom_le G hG hj p .predecessor)
      (giantCandidateModelHitAtom_le G hG hj p .product)
    exact h.trans_eq (by ring)
  have hu₁ (p : U) : u p≤1/2 := by
    apply (hu p).trans
    apply (div_le_iff₀ (Nat.cast_pos.mpr (giantCandidateModelPrime_prime G hG p).pos)).mpr
    linarith only [hlarge p]
  have hsum : (∑ p : U,u p)≤2*(j:ℝ) := by
    calc
      _ ≤ ∑ p : U,(2*(j:ℝ))/(p.val:ℝ) := sum_le_sum (fun p _ => hu p)
      _ = 2*(j:ℝ)*(∑ p : U,1/(p.val:ℝ)) := by
        rw [mul_sum]
        exact sum_congr rfl (fun p _ => (mul_one_div _ _).symm)
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hmass
  have hexp : -(4*(j:ℝ))≤∑ p : U,-(2*u p) := by
    rw [sum_neg_distrib,← mul_sum]
    linarith only [hsum]
  calc
    _ ≤ Real.exp (∑ p : U,-(2*u p)) := Real.exp_le_exp.mpr hexp
    _ = ∏ p : U,Real.exp (-(2*u p)) := Real.exp_sum _ _
    _ ≤ _ := by
      apply prod_le_prod₀ (fun p _ => Real.exp_nonneg _)
      intro p _
      have h := giantCandidate_exp_neg_twice_le_one_sub (hu₀ p) (hu₁ p)
      rw [giantCandidateModelNoHitAtom_eq]
      exact h.trans_eq (by dsimp only [u]; ring)

end
end ArtinMatthews
