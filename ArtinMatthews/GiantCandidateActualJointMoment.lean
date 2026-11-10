module

public import ArtinMatthews.GiantCandidateBoxBinomialMoment
public import ArtinMatthews.GiantCandidateActualPrimeMask
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

/-! Every fixed joint binomial moment of the actual two hit types
transfers to the independent residue model on full rough product dyads. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators

theorem giant_candidate_actual_joint_binomial_moment_eventually
    {ι : Type*} [Fintype ι] (side : ι → GiantCandidateHitSide) (k : ι → ℕ)
    (τ A : ℝ) (hτ : 0<τ) (hA : 0≤A) (j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ G : ι → Finset ℕ,(∀ i,G i ⊆ giantCandidateFullPrimes x) →
      ∃ hG : ∀ i p,p∈G i → p.Prime,
        ∀ H : Fin j → ℕ,(∀ v,x^τ≤(H v:ℝ)) →
        let W := Real.exp ((Real.log x)^(6/25:ℝ))
        let S (v : Fin j) := giantCandidateRoughFullDyad W (H v)
        let ε := (Real.log x)^(-A)
        let m := giantCandidateBoxBinomialMoment S G side k
        let m₀ := giantCandidateModelBinomialMoment j G side k hG
        (1-ε)^j*m₀ ≤ m ∧ m ≤ (1+ε)^j*m₀ := by
  filter_upwards [giant_candidate_actual_prime_mask_eventually τ A hτ hA (∑ i,k i) j,
    giantCandidateFullPrimes_prime_upper_eventually,eventually_gt_atTop (0:ℝ)]
    with x hmask hP hx
  intro G hG
  let hG' (i : ι) (p : ℕ) (hp : p∈G i) : p.Prime := (hP p (hG i hp)).1
  refine ⟨hG',?_⟩
  intro H hH
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let S (v : Fin j) := giantCandidateRoughFullDyad W (H v)
  let ε := (Real.log x)^(-A)
  let E := giantCandidateHitSelections G k
  let hsel (D : E) := giantCandidateSelectionPrimes_prime D.property hG'
  let A₁ (D : E) :=
    ((giantCandidatePrimeTupleMask S (giantCandidateSelectionPrimeMask D.val side (hsel D) j)).card:ℝ)/
      ((Fintype.piFinset S).card:ℝ)
  let A₀ (D : E) :=
    ∏ p : giantCandidateSelectionPrimes D.val,
      ((giantCandidateSelectionPrimeMask D.val side (hsel D) j p).card:ℝ)/(p.val:ℝ)^j
  have hterm (D : E) : (1-ε)^j*A₀ D ≤ A₁ D ∧ A₁ D ≤ (1+ε)^j*A₀ D :=
    (hmask (giantCandidateSelectionPrimes D.val)
      (giantCandidateSelectionPrimes_subset D.property hG)
      (giantCandidateSelectionPrimes_card_le D.property) H
      (giantCandidateSelectionPrimeMask D.val side (hsel D) j) hH).2
  have hS : ∀ t∈Fintype.piFinset S,0<∏ v,t v := by
    intro t ht
    apply prod_pos
    intro v _
    have hHv : 0<H v := Nat.cast_pos.mp ((Real.rpow_pos_of_pos hx τ).trans_le (hH v))
    have hh : t v∈S v := Fintype.mem_piFinset.mp ht v
    exact hHv.trans_le (mem_Ico.mp (mem_filter.mp hh).1).1
  change (1-ε)^j*giantCandidateModelBinomialMoment j G side k hG' ≤ giantCandidateBoxBinomialMoment S G side k ∧
    giantCandidateBoxBinomialMoment S G side k ≤ (1+ε)^j*giantCandidateModelBinomialMoment j G side k hG'
  rw [giantCandidateBoxBinomialMoment_eq_selected S G side k hG' hS]
  change (1-ε)^j*(∑ D : E,A₀ D) ≤ (∑ D : E,A₁ D) ∧
    (∑ D : E,A₁ D) ≤ (1+ε)^j*(∑ D : E,A₀ D)
  simp only [mul_sum]
  exact ⟨sum_le_sum (fun D _ => (hterm D).1),sum_le_sum (fun D _ => (hterm D).2)⟩

end
end ArtinMatthews
