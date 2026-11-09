module

public import ArtinMatthews.GiantCandidateCoinMarginals
public import Mathlib.Algebra.Order.BigOperators.Expect


set_option backward.privateInPublic true
@[expose] public section

/-! Chebyshev for the conditional Bernoulli weights averaged over a finite
box. Off-diagonal covariance enters only through the mixed coin means. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

variable {α ι : Type*} [DecidableEq ι]

private def coinIndicator (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then 1 else 0

private theorem coinIndicator_sum (U : Finset ι) (s : ι → ℝ) {i : ι} (hi : i ∈ U) :
    (∑ S ∈ U.powerset, giantCoinOutcomeWeight U s S * coinIndicator S i) = s i := by
  simpa only [coinIndicator, mul_ite, mul_one, mul_zero, ← Finset.sum_filter] using
    giantCoinOutcomeWeight_single U s hi

private theorem coinIndicator_pair_sum (U : Finset ι) (s : ι → ℝ)
    {i k : ι} (hi : i ∈ U) (hk : k ∈ U) :
    (∑ S ∈ U.powerset, giantCoinOutcomeWeight U s S *
      (coinIndicator S i * coinIndicator S k)) = if i = k then s i else s i * s k := by
  by_cases hik : i = k
  · subst k
    rw [ite_eq_left rfl, ← coinIndicator_sum U s hi]
    apply sum_congr rfl
    intro S _
    by_cases h : i ∈ S <;> simp [coinIndicator, h]
  · rw [ite_eq_right hik, ← giantCoinOutcomeWeight_pair U s hi hk hik, sum_filter]
    apply sum_congr rfl
    intro S _
    by_cases h : i ∈ S <;> by_cases h' : k ∈ S <;> simp [coinIndicator, h, h']

private theorem coinIndicator_centered_sum (U : Finset ι) (s : ι → ℝ)
    {i k : ι} (hi : i ∈ U) (hk : k ∈ U) (a b : ℝ) :
    (∑ S ∈ U.powerset, giantCoinOutcomeWeight U s S *
      ((coinIndicator S i - a) * (coinIndicator S k - b))) =
      (if i = k then s i else s i * s k) - s i * b - a * s k + a * b := by
  calc
    _ = ∑ S ∈ U.powerset, (
        giantCoinOutcomeWeight U s S * (coinIndicator S i * coinIndicator S k) -
        (giantCoinOutcomeWeight U s S * coinIndicator S i) * b -
        a * (giantCoinOutcomeWeight U s S * coinIndicator S k) +
        (a * b) * giantCoinOutcomeWeight U s S) := by
      apply sum_congr rfl
      intro S _
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum,
        ← mul_sum, coinIndicator_pair_sum U s hi hk, coinIndicator_sum U s hi,
        coinIndicator_sum U s hk, giantCoinOutcomeWeight_sum, mul_one]

private theorem coinCount_eq_sum (S F : Finset ι) :
    ((S ∩ F).card : ℝ) = ∑ i ∈ F, coinIndicator S i := by
  have hfilter : F.filter (fun i => i ∈ S) = S ∩ F := by
    ext i
    simp only [mem_filter, mem_inter, and_comm]
  simp only [coinIndicator, Finset.sum_boole, hfilter]

/-- A mixed Bernoulli family has a Chebyshev bound from its averaged
singleton and distinct-pair marginals. The failure sum uses the original
nonnegative outcome weights on the full powerset. -/
theorem giantCoin_family_failure_mean_le (D : Finset α) (hD : D.Nonempty)
    (U F : Finset ι) (hF : F ⊆ U) (hFn : F.Nonempty) (s : α → ι → ℝ)
    {threshold β δ : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hthreshold : threshold ≤ β * (F.card : ℝ) / 2)
    (hs : ∀ t ∈ D, ∀ i ∈ U, s t i ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i ∈ F, β ≤ 𝔼 t ∈ D, s t i)
    (hcov : ∀ i ∈ F, ∀ k ∈ F, i ≠ k →
      |(𝔼 t ∈ D, s t i * s t k) - (𝔼 t ∈ D, s t i) * (𝔼 t ∈ D, s t k)| ≤ δ) :
    (𝔼 t ∈ D, ∑ S ∈ U.powerset.filter (fun S => ((S ∩ F).card : ℝ) < threshold),
      giantCoinOutcomeWeight U (s t) S) ≤ 4 / (β^2 * (F.card : ℝ)) + 4 * δ / β^2 := by
  let μ (i : ι) : ℝ := 𝔼 t ∈ D, s t i
  let m : ℝ := ∑ i ∈ F, μ i
  let n : ℝ := F.card
  let d := β * n / 2
  let C (S : Finset ι) : ℝ := (S ∩ F).card
  let w (t : α) (S : Finset ι) := giantCoinOutcomeWeight U (s t) S
  let E (f : Finset ι → ℝ) : ℝ := 𝔼 t ∈ D, ∑ S ∈ U.powerset, w t S * f S
  let K (i k : ι) (S : Finset ι) :=
    (coinIndicator S i - μ i) * (coinIndicator S k - μ k)
  let B := U.powerset.filter (fun S => C S < threshold)
  have hn : 0 < n := Nat.cast_pos.mpr hFn.card_pos
  have hd : 0 < d := div_pos (mul_pos hβ hn) (by norm_num)
  have hm : β * n ≤ m := by
    simpa only [sum_const, nsmul_eq_mul, n, m, mul_comm β] using
      (sum_le_sum (s := F) (fun i hi => hmean i hi))
  have hw (t : α) (ht : t ∈ D) (S : Finset ι) (hS : S ∈ U.powerset) :
      0 ≤ w t S := giantCoinOutcomeWeight_nonneg U (s t) S (mem_powerset.mp hS) (hs t ht)
  have hcenter (i : ι) (hi : i ∈ F) (k : ι) (hk : k ∈ F) :
      E (K i k) = (𝔼 t ∈ D, if i = k then s t i else s t i * s t k) - μ i * μ k := by
    dsimp only [E, w, K]
    simp_rw [coinIndicator_centered_sum U _ (hF hi) (hF hk)]
    rw [expect_add_distrib, expect_sub_distrib, expect_sub_distrib, ← expect_mul, ← mul_expect,
      expect_const hD]
    change _ - μ i * μ k - μ i * μ k + μ i * μ k = _
    ring
  have hμ (i : ι) (hi : i ∈ F) : μ i ≤ 1 :=
    expect_le hD (fun t ht => (hs t ht i (hF hi)).2)
  have hrow (i : ι) (hi : i ∈ F) : (∑ k ∈ F, E (K i k)) ≤ 1 + δ * n := by
    rw [← add_sum_erase F (fun k => E (K i k)) hi]
    apply add_le_add
    · rw [hcenter i hi i hi]
      simp only [ite_true]
      exact (sub_le_self _ (mul_self_nonneg (μ i))).trans (hμ i hi)
    · calc
        _ ≤ ∑ k ∈ F.erase i, δ := by
          apply sum_le_sum
          intro k hk
          obtain ⟨hne, hk⟩ := mem_erase.mp hk
          rw [hcenter i hi k hk]
          simp only [ite_eq_right hne.symm]
          exact (le_abs_self _).trans (hcov i hi k hk hne.symm)
        _ = ((F.erase i).card : ℝ) * δ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ δ * n := (mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (card_le_card (erase_subset i F))) hδ).trans_eq (mul_comm _ _)
  have hsquare (S : Finset ι) : (C S - m)^2 = ∑ i ∈ F, ∑ k ∈ F, K i k S := by
    rw [show C S = ∑ i ∈ F, coinIndicator S i from coinCount_eq_sum S F]
    dsimp only [m, K]
    rw [← sum_sub_distrib, pow_two, sum_mul]
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
  have hvar : E (fun S => (C S - m)^2) ≤ n + δ * n^2 := by
    calc
      _ = ∑ i ∈ F, ∑ k ∈ F, E (K i k) := by
        dsimp only [E]
        simp_rw [hsquare, Finset.mul_sum,
          Finset.sum_comm (s := U.powerset) (t := F), expect_sum_comm]
      _ ≤ ∑ _i ∈ F, (1 + δ * n) := sum_le_sum hrow
      _ = _ := by rw [sum_const, nsmul_eq_mul]; change n * (1 + δ * n) = _; ring
  have hpoint (t : α) (ht : t ∈ D) :
      d^2 * (∑ S ∈ B, w t S) ≤ ∑ S ∈ U.powerset, w t S * (C S - m)^2 := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ S ∈ B, w t S * (C S - m)^2 := by
        apply sum_le_sum
        intro S hS
        obtain ⟨hSU, hbad⟩ := mem_filter.mp hS
        have hgap : d ≤ m - C S := by
          change C S < threshold at hbad
          change threshold ≤ d at hthreshold
          dsimp only [d] at *
          linarith only [hm, hthreshold, hbad]
        have hsq : d^2 ≤ (C S - m)^2 := by
          rw [show (C S - m)^2 = (m - C S)^2 by ring]
          exact (sq_le_sq₀ hd.le (hd.le.trans hgap)).mpr hgap
        rw [mul_comm (d^2)]
        exact mul_le_mul_of_nonneg_left hsq (hw t ht S hSU)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun S hS _ => mul_nonneg (hw t ht S hS) (sq_nonneg _))
  have hbound := expect_le_expect hpoint
  rw [← mul_expect] at hbound
  change (𝔼 t ∈ D, ∑ S ∈ B, w t S) ≤ _
  calc
    _ ≤ (n + δ * n^2) / d^2 := (le_div_iff₀ (pow_pos hd _)).mpr
      ((mul_comm _ _).le.trans (hbound.trans hvar))
    _ = _ := by
      change (n + δ * n^2) / (β * n / 2)^2 = 4 / (β^2 * n) + 4 * δ / β^2
      field_simp [hβ.ne', hn.ne']
      ring

end
end ArtinMatthews
