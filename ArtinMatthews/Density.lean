module

public import ArtinMatthews.Definitions
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Topology.Order.LiminfLimsup


set_option backward.privateInPublic true
@[expose] public section

/-!
# The relative-density consequence of a dyadic lower bound

This module proves only an implication from `PositiveDyadicLowerBound`. The
analytic lower bound itself is not asserted here. Chebyshev's upper bound for
the prime counting function suffices to obtain positive lower relative density.
-/

open Filter

namespace ArtinMatthews

/-- Number of simultaneous primitive-root primes up to a natural cutoff. -/
noncomputable def primeCount (S : Finset ℤ) (n : ℕ) : ℕ := by
  classical
  exact (n.primesLE.filter fun p => p ∈ SimultaneousPrimitivePrimes S).card

/-- Proportion of the primes up to `n` belonging to the paper's set `P_S`. -/
noncomputable def relativePrimeDensity (S : Finset ℤ) (n : ℕ) : ℝ :=
  (primeCount S n : ℝ) / (Nat.primeCounting n : ℝ)

/-- Positive lower relative density, expressed using natural cutoffs. -/
def PositiveLowerRelativePrimeDensity (S : Finset ℤ) : Prop :=
  0 < liminf (relativePrimeDensity S) atTop

theorem primeCount_le_primeCounting (S : Finset ℤ) (n : ℕ) :
    primeCount S n ≤ Nat.primeCounting n := by
  classical
  simpa only [primeCount, Nat.primesLE_card_eq_primeCounting] using
    (Finset.card_filter_le n.primesLE
      (fun p => p ∈ SimultaneousPrimitivePrimes S))

theorem relativePrimeDensity_nonneg (S : Finset ℤ) (n : ℕ) :
    0 ≤ relativePrimeDensity S n := by
  unfold relativePrimeDensity
  positivity

theorem relativePrimeDensity_le_one (S : Finset ℤ) (n : ℕ) :
    relativePrimeDensity S n ≤ 1 := by
  unfold relativePrimeDensity
  apply div_le_one_of_le₀
  · exact_mod_cast primeCount_le_primeCounting S n
  · positivity

/-- The dyadic interval with right endpoint `n` is contained in the primes up to `n`. -/
theorem dyadicCount_half_le_primeCount (S : Finset ℤ) (n : ℕ) :
    dyadicCount S ((n : ℝ) / 2) ≤ primeCount S n := by
  classical
  unfold dyadicCount primeCount
  apply Finset.card_le_card
  intro p hp
  obtain ⟨_, _, hright, hprime⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_, hprime.1⟩, hprime⟩
  have : (p : ℝ) ≤ (n : ℝ) := by linarith
  exact_mod_cast this

/-- A dyadic lower bound gives a uniform positive proportion of all primes
for all sufficiently large natural cutoffs. -/
theorem PositiveDyadicLowerBound.eventually_relativePrimeDensity_ge
    {S : Finset ℤ} (h : PositiveDyadicLowerBound S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, δ ≤ relativePrimeDensity S n := by
  obtain ⟨c, hc, x₀, hx₀, hbound⟩ := h
  let K : ℝ := Real.log 4 + 1
  have hK : 0 < K := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp [K]
    linarith
  refine ⟨c / (2 * K), by positivity, ?_⟩
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 * x₀ ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (2 * x₀))
  have hCheb : ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ K * (n : ℝ) / Real.log (n : ℝ) := by
    simpa only [Nat.floor_natCast] using
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
        (Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num)))
  filter_upwards [hlarge, hCheb] with n hn hπ
  have hn2 : 1 < (n : ℝ) / 2 := by linarith
  have hnpos : 0 < (n : ℝ) := by linarith
  have hloghalf : 0 < Real.log ((n : ℝ) / 2) := Real.log_pos hn2
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlogs : Real.log ((n : ℝ) / 2) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) (by linarith)
  have hdyadic : c * ((n : ℝ) / 2) / Real.log ((n : ℝ) / 2) ≤
      (primeCount S n : ℝ) :=
    (hbound ((n : ℝ) / 2) (by linarith)).trans
      (by exact_mod_cast dyadicCount_half_le_primeCount S n)
  have hcount : c * (n : ℝ) / (2 * Real.log (n : ℝ)) ≤ (primeCount S n : ℝ) := by
    calc
      c * (n : ℝ) / (2 * Real.log (n : ℝ)) =
          (c * ((n : ℝ) / 2)) / Real.log (n : ℝ) := by ring
      _ ≤ (c * ((n : ℝ) / 2)) / Real.log ((n : ℝ) / 2) :=
        div_le_div_of_nonneg_left (by positivity) hloghalf hlogs
      _ ≤ _ := hdyadic
  have hπpos : 0 < (Nat.primeCounting n : ℝ) := by
    have hcountpos : 0 < (primeCount S n : ℝ) :=
      lt_of_lt_of_le (by positivity : 0 < c * (n : ℝ) / (2 * Real.log (n : ℝ))) hcount
    exact hcountpos.trans_le (by exact_mod_cast primeCount_le_primeCounting S n)
  unfold relativePrimeDensity
  calc
    c / (2 * K) =
        (c * (n : ℝ) / (2 * Real.log (n : ℝ))) /
          (K * (n : ℝ) / Real.log (n : ℝ)) := by
      field_simp
    _ ≤ _ := div_le_div₀ (by positivity) hcount hπpos hπ

/-- A proved dyadic lower bound implies positive lower relative prime density. -/
theorem PositiveDyadicLowerBound.positiveLowerRelativePrimeDensity
    {S : Finset ℤ} (h : PositiveDyadicLowerBound S) :
    PositiveLowerRelativePrimeDensity S := by
  obtain ⟨δ, hδ, hδeventually⟩ := h.eventually_relativePrimeDensity_ge
  exact hδ.trans_le (le_liminf_of_le
    (isCoboundedUnder_ge_of_le atTop (relativePrimeDensity_le_one S)) hδeventually)

end ArtinMatthews
