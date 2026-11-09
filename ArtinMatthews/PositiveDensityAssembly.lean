module

public import ArtinMatthews.SieveAssembly
public import ArtinMatthews.RealDensity


set_option backward.privateInPublic true
@[expose] public section

/-!
# Conditional assembly of the final positive-density argument

This module implements the last subtraction in Section 10.3. The weighted
candidate lower bound and the small-index upper bound are explicit analytic
hypotheses about the actual finite candidate sets. The latter may contain an
`o(x / log x)` remainder. The large-index loss is discharged by the proved
exceptional-product estimate.

No assertion here supplies those analytic hypotheses from the failure of the
finite obstructions. In particular, this is an assembly implication, not a
proof of the main theorem.
-/

open Filter
open scoped Topology

namespace ArtinMatthews

/-- An eventual real-cutoff lower bound has the threshold form used in (1.1). -/
theorem positiveDyadicLowerBound_of_eventually {S : Finset ℤ} {c : ℝ}
    (hc : 0 < c)
    (hbound : ∀ᶠ x : ℝ in atTop, c * (x / Real.log x) ≤ (dyadicCount S x : ℝ)) :
    PositiveDyadicLowerBound S := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hbound
  refine ⟨c, hc, max x₀ 2, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _)
  · intro x hx
    simpa only [mul_div_assoc] using hx₀ x ((le_max_left x₀ 2).trans hx)

/-- Final sieve subtraction with all unproved analytic inputs exposed.

`P x` and `w x` are the actual candidate primes and their weights. Their
primality, interval support, nonzero residues, large-prime factorization and
weight range are separate hypotheses. The candidate count has main coefficient
`c`; the small-index loss has coefficient `b < c` and a little-oh remainder.
The theorem proves the positive dyadic bound with coefficient `(c - b) / 2`.
The restriction on `ε` is precisely what the elementary final product needs;
any stricter range required to establish the input estimates belongs in their
proofs. -/
theorem positiveDyadicLowerBound_of_weighted_sieve_inputs
    {S : Finset ℤ} (hS : AdmissibleBases S)
    {ε c b : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) (_hc : 0 < c) (hbc : b < c)
    (P : ℝ → Finset ℕ) (w : ℝ → ℕ → ℝ) (error : ℝ → ℝ)
    (hprime : ∀ᶠ x : ℝ in atTop, ∀ p ∈ P x, p.Prime)
    (hinterval : ∀ᶠ x : ℝ in atTop,
      ∀ p ∈ P x, x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x)
    (hnonzero : ∀ᶠ x : ℝ in atTop,
      ∀ p ∈ P x, ∀ a ∈ S, (a : ZMod p) ≠ 0)
    (hfactor : ∀ᶠ x : ℝ in atTop, ∀ p ∈ P x,
      ∃ k Q : ℕ, Q.Prime ∧ p - 1 = k * Q ∧ k ≤ exceptionalExponentCutoff ε x)
    (hweights : ∀ᶠ x : ℝ in atTop, ∀ p ∈ P x, 0 ≤ w x p ∧ w x p ≤ 1)
    (hcandidate : ∀ᶠ x : ℝ in atTop,
      c * (x / Real.log x) ≤ ∑ p ∈ P x, w x p)
    (hsmall : ∀ᶠ x : ℝ in atTop,
      ((smallIndexCandidates S (P x) (exceptionalExponentCutoff ε x)).card : ℝ) ≤
        b * (x / Real.log x) + error x)
    (herror : error =o[atTop] (fun x : ℝ => x / Real.log x)) :
    PositiveDyadicLowerBound S := by
  have hgap : 0 < c - b := sub_pos.mpr hbc
  have hquarter : 0 < (c - b) / 4 := by positivity
  have herrorSmall : ∀ᶠ x : ℝ in atTop,
      error x / (x / Real.log x) < (c - b) / 4 :=
    (tendsto_order.mp herror.tendsto_div_nhds_zero).2 _ hquarter
  have hexceptionSmall : ∀ᶠ x : ℝ in atTop,
      (exceptionalPrimeCount S ε x : ℝ) / (x / Real.log x) < (c - b) / 4 :=
    (tendsto_order.mp (tendsto_exceptionalPrimeCount_div hS hε hεhalf)).2 _ hquarter
  apply positiveDyadicLowerBound_of_eventually (c := (c - b) / 2) (by positivity)
  filter_upwards [hprime, hinterval, hnonzero, hfactor, hweights, hcandidate, hsmall,
    herrorSmall, hexceptionSmall, eventually_gt_atTop (1 : ℝ)] with
    x hp hi hn hf hw hA hB hr hE hx
  have hxlog : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx)
  have hr' : error x ≤ (c - b) / 4 * (x / Real.log x) :=
    ((div_lt_iff₀ hxlog).mp hr).le
  have hE' : (exceptionalPrimeCount S ε x : ℝ) ≤
      (c - b) / 4 * (x / Real.log x) := ((div_lt_iff₀ hxlog).mp hE).le
  have hsieve := dyadicCount_ge_of_weighted_candidates hS hp hi hn hf hw hA hB hE'
  change c * (x / Real.log x) - (b * (x / Real.log x) + error x) -
      (c - b) / 4 * (x / Real.log x) ≤ (dyadicCount S x : ℝ) at hsieve
  nlinarith

/-- The same explicit analytic inputs yield both the dyadic conclusion and
positive lower relative prime density, with natural and real cutoffs. -/
theorem weighted_sieve_inputs_imply_positive_density
    {S : Finset ℤ} (hS : AdmissibleBases S)
    {ε c b : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hc : 0 < c) (hbc : b < c)
    (P : ℝ → Finset ℕ) (w : ℝ → ℕ → ℝ) (error : ℝ → ℝ)
    (hprime : ∀ᶠ x : ℝ in atTop, ∀ p ∈ P x, p.Prime)
    (hinterval : ∀ᶠ x : ℝ in atTop,
      ∀ p ∈ P x, x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x)
    (hnonzero : ∀ᶠ x : ℝ in atTop,
      ∀ p ∈ P x, ∀ a ∈ S, (a : ZMod p) ≠ 0)
    (hfactor : ∀ᶠ x : ℝ in atTop, ∀ p ∈ P x,
      ∃ k Q : ℕ, Q.Prime ∧ p - 1 = k * Q ∧ k ≤ exceptionalExponentCutoff ε x)
    (hweights : ∀ᶠ x : ℝ in atTop, ∀ p ∈ P x, 0 ≤ w x p ∧ w x p ≤ 1)
    (hcandidate : ∀ᶠ x : ℝ in atTop,
      c * (x / Real.log x) ≤ ∑ p ∈ P x, w x p)
    (hsmall : ∀ᶠ x : ℝ in atTop,
      ((smallIndexCandidates S (P x) (exceptionalExponentCutoff ε x)).card : ℝ) ≤
        b * (x / Real.log x) + error x)
    (herror : error =o[atTop] (fun x : ℝ => x / Real.log x)) :
    PositiveDyadicLowerBound S ∧ PositiveLowerRelativePrimeDensity S ∧
      PositiveRealLowerRelativePrimeDensity S := by
  have hdyadic := positiveDyadicLowerBound_of_weighted_sieve_inputs
    hS hε hεhalf hc hbc P w error hprime hinterval hnonzero hfactor hweights hcandidate hsmall herror
  exact ⟨hdyadic, hdyadic.positiveLowerRelativePrimeDensity,
    hdyadic.positiveRealLowerRelativePrimeDensity⟩

end ArtinMatthews
