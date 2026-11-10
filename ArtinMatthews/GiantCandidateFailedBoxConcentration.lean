module

public import ArtinMatthews.GiantCandidateFailedDyadLimit
public import ArtinMatthews.GiantCandidateCoinConcentration
public import ArtinMatthews.GiantCandidateFailedDyadCard
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The two literal success-count tests give uniform decay of the
failed coin mass on full rough boxes. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped BigOperators

theorem giantCandidateFailedBoxMean_le_of_success_moments {j : ℕ}
    (x threshold c q : ℝ) (H : Fin j → ℕ) {β δ : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hD : (giantCandidateFullRoughBox x H).Nonempty)
    (hsmall : (giantCandidateCoinSmall x).Nonempty)
    (hbig : (giantCandidateCoinBig x).Nonempty)
    (hsmall_threshold : threshold * Real.log (Real.log x) ≤
      β * ((giantCandidateCoinSmall x).card : ℝ) / 2)
    (hbig_threshold : threshold * Real.log (Real.log x) ≤
      β * ((giantCandidateCoinBig x).card : ℝ) / 2)
    (hs : ∀ (i : GiantCandidateGroupIndex x) (v : ℕ),
      giantCandidateCoinSuccess x c q j v i ∈ Set.Icc (0 : ℝ) 1)
    (hmoments :
      let s (t : Fin j → ℕ) (g : GiantCandidateGroupIndex x) :=
        giantCandidateCoinSuccess x c q j (∏ i, t i) g
      let D := giantCandidateFullRoughBox x H
      (∀ g, β ≤ 𝔼 t ∈ D, s t g) ∧
      (∀ g k, g ≠ k →
        |(𝔼 t ∈ D, s t g * s t k) - (𝔼 t ∈ D, s t g) * (𝔼 t ∈ D, s t k)| ≤ δ)) :
    giantCandidateFailedBoxMean x threshold c q H ≤
      4 / (β^2 * ((giantCandidateCoinSmall x).card : ℝ)) +
      4 / (β^2 * ((giantCandidateCoinBig x).card : ℝ)) + 8 * δ / β^2 := by
  let D := giantCandidateFullRoughBox x H
  let U : Finset (GiantCandidateGroupIndex x) := univ
  let A := giantCandidateCoinSmall x
  let B := giantCandidateCoinBig x
  let a := threshold * Real.log (Real.log x)
  let s (t : Fin j → ℕ) (g : GiantCandidateGroupIndex x) :=
    giantCandidateCoinSuccess x c q j (∏ i, t i) g
  let w (t : Fin j → ℕ) (S : Finset (GiantCandidateGroupIndex x)) :=
    giantCoinOutcomeWeight U (s t) S
  let fail (F : Finset (GiantCandidateGroupIndex x)) (t : Fin j → ℕ) :=
    ∑ S ∈ U.powerset.filter (fun S => ((S ∩ F).card : ℝ) < a), w t S
  have hbad : U.powerset \ giantCandidateRetainedOutcomes x threshold =
      U.powerset.filter (fun S => ((S ∩ A).card : ℝ) < a ∨ ((S ∩ B).card : ℝ) < a) := by
    ext S
    constructor
    · intro hS
      obtain ⟨hU, hR⟩ := Finset.mem_sdiff.mp hS
      refine mem_filter.mpr ⟨hU, ?_⟩
      have hn : ¬(a ≤ ((S ∩ A).card : ℝ) ∧ a ≤ ((S ∩ B).card : ℝ)) :=
        fun h => hR (mem_giantCandidateRetainedOutcomes.mpr h)
      exact (not_and_or.mp hn).imp lt_of_not_ge lt_of_not_ge
    · intro hS
      obtain ⟨hU, hR⟩ := mem_filter.mp hS
      refine Finset.mem_sdiff.mpr ⟨hU, ?_⟩
      intro hSret
      obtain ⟨hA, hB⟩ := mem_giantCandidateRetainedOutcomes.mp hSret
      exact hR.elim (not_lt_of_ge hA) (not_lt_of_ge hB)
  have hsplit (t : Fin j → ℕ) :
      giantCandidateFailedCoinMass x threshold c q j (∏ i, t i) ≤ fail A t + fail B t := by
    change (∑ S ∈ U.powerset \ giantCandidateRetainedOutcomes x threshold, w t S) ≤ _
    rw [hbad]
    simp only [fail, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro S hS
    have hw : 0 ≤ w t S := giantCoinOutcomeWeight_nonneg U (s t) S (mem_powerset.mp hS)
      (fun g _ => hs g (∏ i, t i))
    by_cases hA : ((S ∩ A).card : ℝ) < a <;> by_cases hB : ((S ∩ B).card : ℝ) < a <;>
      simp [hA, hB, hw]
  obtain ⟨hm, hc⟩ := hmoments
  have hb (F : Finset (GiantCandidateGroupIndex x)) (hF : F.Nonempty)
      (hFthreshold : a ≤ β * (F.card : ℝ) / 2) :
      (𝔼 t ∈ D, fail F t) ≤ 4 / (β^2 * (F.card : ℝ)) + 4 * δ / β^2 :=
    giantCoin_family_failure_mean_le D hD U F (subset_univ F) hF s hβ hδ hFthreshold
      (fun t _ g _ => hs g (∏ i, t i)) (fun g _ => hm g)
      (fun g _ k _ hgk => hc g k hgk)
  have hA := hb A hsmall hsmall_threshold
  have hB := hb B hbig hbig_threshold
  change giantCandidateFailedBoxMean x threshold c q H ≤
    4 / (β^2 * (A.card : ℝ)) + 4 / (β^2 * (B.card : ℝ)) + 8 * δ / β^2
  calc
    _ = 𝔼 t ∈ D, giantCandidateFailedCoinMass x threshold c q j (∏ i, t i) :=
      (expect_eq_sum_div_card D _).symm
    _ ≤ 𝔼 t ∈ D, (fail A t + fail B t) := expect_le_expect (fun t _ => hsplit t)
    _ = (𝔼 t ∈ D, fail A t) + (𝔼 t ∈ D, fail B t) := expect_add_distrib _ _ _
    _ ≤ _ := by
      calc
        _ ≤ (4 / (β^2 * (A.card : ℝ)) + 4 * δ / β^2) +
            (4 / (β^2 * (B.card : ℝ)) + 4 * δ / β^2) := add_le_add hA hB
        _ = _ := by ring

theorem giant_candidate_uniformFailedBoxDecay_of_success_moments
    {γ q β : ℝ} (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) (hj : 0 < j)
    (hβ : 0 < β)
    (hmoments : ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop,
      ∀ H : Fin j → ℕ, (∀ i, x^(γ/2) ≤ (H i : ℝ)) →
        let s (t : Fin j → ℕ) (g : GiantCandidateGroupIndex x) :=
          giantCandidateCoinSuccess x (giantCandidateCoinScale q j) q j (∏ i, t i) g
        let D := giantCandidateFullRoughBox x H
        (∀ g, β ≤ 𝔼 t ∈ D, s t g) ∧
        (∀ g k, g ≠ k →
          |(𝔼 t ∈ D, s t g * s t k) - (𝔼 t ∈ D, s t g) * (𝔼 t ∈ D, s t k)| ≤ δ)) :
    ∃ threshold : ℝ, 0 < threshold ∧ GiantCandidateUniformFailedBoxDecay γ q threshold j := by
  let rate : ℝ := (45/100 - 40/100) / (2 * Real.log 2)
  let threshold := β * rate / 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrate : 0 < rate := div_pos (by norm_num) (by positivity)
  have hslopes : rate ≤ (35/100 - 28/100) / (2 * Real.log 2) :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  refine ⟨threshold, div_pos (mul_pos hβ hrate) (by norm_num), ?_⟩
  intro ε hε
  let δ := β^2 * ε / 16
  let N := 16 / (β^2 * ε)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hN : 0 < N := by dsimp only [N]; positivity
  filter_upwards [hmoments δ hδ, giantCandidateGroup_counts_eventually,
    giantCandidateFullRoughBox_card_eventually (half_pos hγ) j,
    giantCandidateCoinSuccess_actual_unitInterval hq0 hq1 j hj,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (N / rate)]
    with x hμ hgroups hbox hs hlog
  intro H hH
  let L := Real.log (Real.log x)
  let A := giantCandidateCoinSmall x
  let B := giantCandidateCoinBig x
  have hL : 0 ≤ L := (div_nonneg hN.le hrate.le).trans hlog
  have hLA : rate * L ≤ (A.card : ℝ) := by
    rw [giantCandidateCoinSmall_card]
    exact (mul_le_mul_of_nonneg_right hslopes hL).trans hgroups.1
  have hLB : rate * L ≤ (B.card : ℝ) := by
    rw [giantCandidateCoinBig_card]
    exact hgroups.2.2.1
  have hNL : N ≤ rate * L := by
    rw [mul_comm]
    exact (div_le_iff₀ hrate).mp hlog
  have hA := hNL.trans hLA
  have hB := hNL.trans hLB
  have hcardA : A.Nonempty := card_pos.mp (Nat.cast_pos.mp (hN.trans_le hA))
  have hcardB : B.Nonempty := card_pos.mp (Nat.cast_pos.mp (hN.trans_le hB))
  have ht (n : ℕ) (hn : rate * L ≤ (n : ℝ)) : threshold * L ≤ β * (n : ℝ) / 2 := by
    calc
      _ = β * (rate * L) / 2 := by dsimp only [threshold]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn hβ.le) (by norm_num)
  have hnBound (n : ℕ) (hn : N ≤ (n : ℝ)) : 4 / (β^2 * (n : ℝ)) ≤ ε / 4 := by
    have hn0 : 0 < (n : ℝ) := hN.trans_le hn
    have hβ2 := pow_pos hβ 2
    apply (div_le_iff₀ (mul_pos hβ2 hn0)).mpr
    have h := (div_le_iff₀ (mul_pos hβ2 hε)).mp hn
    nlinarith only [h]
  have hδEq : 8 * δ / β^2 = ε / 2 := by
    dsimp only [δ]
    field_simp [hβ.ne']
    ring
  have hm := giantCandidateFailedBoxMean_le_of_success_moments x threshold
    (giantCandidateCoinScale q j) q H hβ hδ.le (card_pos.mp (hbox H hH).1)
    hcardA hcardB (ht _ hLA) (ht _ hLB) hs (hμ H hH)
  apply hm.trans
  rw [hδEq]
  linarith only [hnBound _ hA, hnBound _ hB]

end
end ArtinMatthews
