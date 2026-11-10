module

public import ArtinMatthews.GiantCandidateFailedBoxMean
public import ArtinMatthews.GiantCandidateActualCoinCompare
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Rat.Star
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

/-! The literal per-box means and pair means inherit small covariance
from the exact factorization of the two model groups. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators

private theorem giantCandidate_expect_mem_unitInterval {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ t∈S,f t∈Set.Icc (0:ℝ) 1) :
    (𝔼 t∈S,f t)∈Set.Icc (0:ℝ) 1 := by
  refine ⟨expect_nonneg (fun t ht => (hf t ht).1),?_⟩
  by_cases hS : S.Nonempty
  · exact (expect_le_expect (fun t ht => (hf t ht).2)).trans_eq (expect_const hS 1)
  · rw [not_nonempty_iff_eq_empty.mp hS,expect_empty]
    exact zero_le_one

theorem giant_candidate_box_coin_covariance_eventually (τ : ℝ) (hτ : 0<τ)
    {q : ℝ} (hq₀ : 0≤q) (hq₁ : q<1) {j : ℕ} (hj : 0<j) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ x : ℝ in atTop,∀ H : Fin j → ℕ,(∀v,x^τ≤(H v:ℝ)) →
      let S := giantCandidateFullRoughBox x H
      let s (t : Fin j → ℕ) (g : GiantCandidateGroupIndex x) :=
        giantCandidateCoinSuccess x (giantCandidateCoinScale q j) q j (∏v,t v) g
      ∀ g h : GiantCandidateGroupIndex x,g≠h →
        |(𝔼 t∈S,s t g*s t h)-(𝔼 t∈S,s t g)*(𝔼 t∈S,s t h)|≤δ := by
  have hδ₃ : 0<δ/3 := div_pos hδ (by norm_num)
  filter_upwards [giant_candidate_actual_single_coin_compare_eventually τ hτ hq₀ hq₁ hj hδ₃,
    giant_candidate_actual_pair_coin_compare_eventually τ hτ hq₀ hq₁ hj hδ₃,
    giantCandidateCoinSuccess_actual_unitInterval hq₀ hq₁ j hj,
    giantCandidateGroup_mass_eventually,giantCandidateFullPrimes_prime_upper_eventually]
    with x hsingle hpair hcoin hmass hP
  intro H hH S s g h hgh
  let P := giantCandidateGroup x g
  let Q := giantCandidateGroup x h
  let hp (p : ℕ) (hp : p∈P) : p.Prime := (hP p (mem_giantCandidateFullPrimes.mpr ⟨g,hp⟩)).1
  let hq (p : ℕ) (hp : p∈Q) : p.Prime := (hP p (mem_giantCandidateFullPrimes.mpr ⟨h,hp⟩)).1
  let c := giantCandidateCoinScale q j
  let a := 𝔼 t∈S,s t g
  let b := 𝔼 t∈S,s t h
  let d := 𝔼 t∈S,s t g*s t h
  let A := giantCandidateSingleModelCoinMean P hp c q j
  let B := giantCandidateSingleModelCoinMean Q hq c q j
  have ha : |a-A|≤δ/3 := hsingle g hp H hH
  have hb : |b-B|≤δ/3 := hsingle h hq H hH
  have hd : |d-A*B|≤δ/3 := hpair g h hgh hp hq H hH
  have hbU : b∈Set.Icc (0:ℝ) 1 :=
    giantCandidate_expect_mem_unitInterval S (fun t => s t h) (fun t _ => hcoin h (∏v,t v))
  have hAU : A∈Set.Icc (0:ℝ) 1 :=
    giantCandidateSingleModelCoinMean_unitInterval P hp hq₀ hq₁ j hj (hmass g).1.le
  have hprod : |a*b-A*B|≤δ/3+δ/3 := by
    rw [show a*b-A*B=(a-A)*b+A*(b-B) by ring]
    calc
      _ ≤ |a-A| * |b|+|A| * |b-B| := by
        simpa only [abs_mul] using abs_add_le ((a-A)*b) (A*(b-B))
      _ ≤ _ := by
        rw [abs_of_nonneg hbU.1,abs_of_nonneg hAU.1]
        exact add_le_add ((mul_le_of_le_one_right (abs_nonneg _) hbU.2).trans ha)
          ((mul_le_of_le_one_left (abs_nonneg _) hAU.2).trans hb)
  change |d-a*b|≤δ
  have htri := abs_sub_le d (A*B) (a*b)
  rw [abs_sub_comm (A*B) (a*b)] at htri
  linarith only [htri,hd,hprod]

end
end ArtinMatthews
