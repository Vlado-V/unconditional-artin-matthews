module

public import ArtinMatthews.GiantCandidateFailedBoxMean
public import ArtinMatthews.GiantCandidateCoinModel
public import ArtinMatthews.GiantCandidateCoinModelPair
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

/-! The actual one- and two-group coin tests agree uniformly with
their independent model means. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators

theorem giant_candidate_actual_single_coin_compare_eventually (τ : ℝ) (hτ : 0<τ)
    {q : ℝ} (hq₀ : 0≤q) (hq₁ : q<1) {j : ℕ} (hj : 0<j) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ x : ℝ in atTop,∀ g : GiantCandidateGroupIndex x,
      ∀ hp : ∀p∈giantCandidateGroup x g,p.Prime,
      ∀ H : Fin j → ℕ,(∀v,x^τ≤(H v:ℝ)) →
      |(𝔼 t∈giantCandidateFullRoughBox x H,
          giantCandidateCoinSuccess x (giantCandidateCoinScale q j) q j (∏v,t v) g)-
        giantCandidateSingleModelCoinMean (giantCandidateGroup x g) hp
          (giantCandidateCoinScale q j) q j|≤δ := by
  filter_upwards [giant_candidate_actual_group_tests_uniform 1 τ hτ hj hδ,
    giantCandidateGroup_mass_eventually] with x htest hmass
  intro g hp H hH
  let g' : Fin 1 → GiantCandidateGroupIndex x := fun _ => g
  let A : Fin 1 → Finset ℕ := fun i => giantCandidateGroup x (g' i)
  let c := giantCandidateCoinScale q j
  let f := giantCandidateCoinCountTest A c q j 0
  have hinj : Function.Injective g' := fun i l _ => Subsingleton.elim i l
  obtain ⟨hPrime,h⟩ := htest g' hinj
  have hf (k : Fin 1 × Bool → ℕ) : |f k|≤1 := by
    have hu := giantCandidateCoinCountTest_unitInterval A hq₀ hq₁ hj 0 (hmass g).1.le k
    exact (abs_of_nonneg hu.1).trans_le hu.2
  have hh := h H hH f hf
  change |(𝔼 t∈giantCandidateFullRoughBox x H,
    f (giantCandidateActualHitCounts (giantCandidateCoinModelBands A) (giantCandidateCoinModelSides 1) t))-
      giantCandidateSingleModelCoinMean (giantCandidateGroup x g) hp c q j|≤δ at hh
  dsimp only [f,A] at hh
  simp_rw [giantCandidateCoinCountTest_actual] at hh
  exact hh

private theorem giantCandidatePairModelCoinMean_eq_bands (A : Fin 2 → Finset ℕ) (P Q : Finset ℕ)
    (h₀ : A 0=P) (h₁ : A 1=Q)
    (hp : ∀ p∈P,p.Prime) (hq : ∀ p∈Q,p.Prime) (hd : Disjoint P Q)
    (hA : ∀ i p,p∈giantCandidateCoinModelBands A i → p.Prime)
    (c q : ℝ) (j : ℕ) :
    (𝔼 t∈giantCandidateModelResidueTuples (giantCandidateCoinModelBands A) hA j,
      giantCandidateCoinModelValue A c q j 0 t*giantCandidateCoinModelValue A c q j 1 t) =
      giantCandidateSingleModelCoinMean P hp c q j*giantCandidateSingleModelCoinMean Q hq c q j := by
  have he : A=giantCandidateTwoBands P Q := by
    funext i
    fin_cases i
    · exact h₀.trans (giantCandidateTwoBands_zero P Q).symm
    · exact h₁.trans (giantCandidateTwoBands_one P Q).symm
  subst A
  exact giantCandidatePairModelCoinMean_eq P Q hp hq hd hA c q j

theorem giant_candidate_actual_pair_coin_compare_eventually (τ : ℝ) (hτ : 0<τ)
    {q : ℝ} (hq₀ : 0≤q) (hq₁ : q<1) {j : ℕ} (hj : 0<j) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ x : ℝ in atTop,∀ g h : GiantCandidateGroupIndex x,g≠h →
      ∀ hp : ∀p∈giantCandidateGroup x g,p.Prime,
      ∀ hq : ∀p∈giantCandidateGroup x h,p.Prime,
      ∀ H : Fin j → ℕ,(∀v,x^τ≤(H v:ℝ)) →
      |(𝔼 t∈giantCandidateFullRoughBox x H,
        giantCandidateCoinSuccess x (giantCandidateCoinScale q j) q j (∏v,t v) g*
          giantCandidateCoinSuccess x (giantCandidateCoinScale q j) q j (∏v,t v) h)-
        giantCandidateSingleModelCoinMean (giantCandidateGroup x g) hp (giantCandidateCoinScale q j) q j*
          giantCandidateSingleModelCoinMean (giantCandidateGroup x h) hq (giantCandidateCoinScale q j) q j|≤δ := by
  filter_upwards [giant_candidate_actual_group_tests_uniform 2 τ hτ hj hδ,
    giantCandidateGroup_mass_eventually,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with x htest hmass hx hL
  intro g h hgh hp hq H hH
  let g' (i : Fin 2) := if i=0 then g else h
  let A : Fin 2 → Finset ℕ := fun i => giantCandidateGroup x (g' i)
  let P := giantCandidateGroup x g
  let Q := giantCandidateGroup x h
  let c := giantCandidateCoinScale q j
  let f₀ := giantCandidateCoinCountTest A c q j 0
  let f₁ := giantCandidateCoinCountTest A c q j 1
  let f (k : Fin 2 × Bool → ℕ) := f₀ k*f₁ k
  have hg₀ : g' 0=g := ite_eq_left rfl
  have hg₁ : g' 1=h := ite_eq_right (by decide)
  have hA₀ : A 0=P := congrArg (giantCandidateGroup x) hg₀
  have hA₁ : A 1=Q := congrArg (giantCandidateGroup x) hg₁
  have hinj : Function.Injective g' := by
    intro i l he
    fin_cases i <;> fin_cases l
    · rfl
    · exact (hgh (hg₀.symm.trans (he.trans hg₁))).elim
    · exact (hgh (hg₀.symm.trans (he.symm.trans hg₁))).elim
    · rfl
  obtain ⟨hPrime,hcomp⟩ := htest g' hinj
  have hf (k : Fin 2 × Bool → ℕ) : |f k|≤1 := by
    have hf₀ := giantCandidateCoinCountTest_unitInterval A hq₀ hq₁ hj 0
      (show Real.log 2/2≤bandReciprocalMass (A 0) by rw [hA₀]; exact (hmass g).1.le) k
    have hf₁ := giantCandidateCoinCountTest_unitInterval A hq₀ hq₁ hj 1
      (show Real.log 2/2≤bandReciprocalMass (A 1) by rw [hA₁]; exact (hmass h).1.le) k
    change |f₀ k*f₁ k|≤1
    rw [abs_of_nonneg (mul_nonneg hf₀.1 hf₁.1)]
    exact (mul_le_of_le_one_left hf₁.1 hf₀.2).trans hf₁.2
  have hh := hcomp H hH f hf
  have hm := giantCandidatePairModelCoinMean_eq_bands A P Q hA₀ hA₁ hp hq
    (giantCandidateGroup_pairwise_disjoint hx hL hgh) hPrime c q j
  change |(𝔼 t∈giantCandidateFullRoughBox x H,
    f (giantCandidateActualHitCounts (giantCandidateCoinModelBands A) (giantCandidateCoinModelSides 2) t))-
      (𝔼 t∈giantCandidateModelResidueTuples (giantCandidateCoinModelBands A) hPrime j,
        giantCandidateCoinModelValue A c q j 0 t*giantCandidateCoinModelValue A c q j 1 t)|≤δ at hh
  rw [hm] at hh
  dsimp only [f,f₀,f₁,A] at hh
  simp_rw [giantCandidateCoinCountTest_actual,hg₀,hg₁] at hh
  exact hh

end
end ArtinMatthews
