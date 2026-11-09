module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A smooth test supported away from zero makes the small-prime cutoff
in the finite positive sieve eventually irrelevant. No bound on the marked
weight itself is needed for this exact support argument. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

theorem marked_power_cutoff_below_support {a γ : ℝ} (ha : 0 < a) (hγ : γ < 1) :
    ∀ᶠ x : ℝ in atTop, (⌊x ^ γ⌋₊ : ℝ) < a * x := by
  have hlim : Tendsto (fun x : ℝ => x ^ (γ - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - γ))
  filter_upwards [hlim.eventually (gt_mem_nhds ha), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have heq : x ^ γ = x * x ^ (γ - 1) := by
    calc
      x ^ γ = x ^ (1 + (γ - 1)) := by congr 1; ring
      _ = x ^ (1 : ℝ) * x ^ (γ - 1) := Real.rpow_add hx0 _ _
      _ = _ := by rw [Real.rpow_one]
  apply (Nat.floor_le (Real.rpow_nonneg hx0.le γ)).trans_lt
  rw [heq]
  nlinarith

/-- The cutoff removes only terms on which the test function is zero. -/
theorem marked_prime_cutoff_sum_eq (U : Finset ℕ) (H : ℕ → ℝ) (Φ : ℝ → ℝ)
    {x a : ℝ} {v : ℕ} (hx : 0 < x) (hcut : (v : ℝ) < a * x)
    (hlow : ∀ t < a, Φ t = 0) :
    (∑ u ∈ U.filter (fun u => (u + 1).Prime ∧ v < u + 1), Φ ((u : ℝ) / x) * H u) =
      ∑ u ∈ U.filter (fun u => (u + 1).Prime), Φ ((u : ℝ) / x) * H u := by
  classical
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hp : (u + 1).Prime
  · by_cases hv : v < u + 1
    · simp [hp, hv]
    · have hu : u < v := by omega
      have huR : (u : ℝ) < v := by exact_mod_cast hu
      have hz := hlow ((u : ℝ) / x) ((div_lt_iff₀ hx).mpr (huR.trans hcut))
      simp [hp, hv, hz]
  · simp [hp]

/-- Exact eventual removal of the cutoff for arbitrary changing finite
supports and marked weights, using only support away from zero. -/
theorem marked_prime_cutoff_eq_eventually (U : ℝ → Finset ℕ) (H : ℝ → ℕ → ℝ)
    (Φ : ℝ → ℝ) {a γ : ℝ} (ha : 0 < a) (hγ : γ < 1)
    (hlow : ∀ t < a, Φ t = 0) :
    ∀ᶠ x : ℝ in atTop,
      (∑ u ∈ (U x).filter (fun u => (u + 1).Prime ∧ ⌊x ^ γ⌋₊ < u + 1),
        Φ ((u : ℝ) / x) * H x u) =
      ∑ u ∈ (U x).filter (fun u => (u + 1).Prime), Φ ((u : ℝ) / x) * H x u := by
  filter_upwards [marked_power_cutoff_below_support ha hγ, eventually_gt_atTop (0 : ℝ)] with x hcut hx
  exact marked_prime_cutoff_sum_eq (U x) (H x) Φ hx hcut hlow

end ArtinMatthews
