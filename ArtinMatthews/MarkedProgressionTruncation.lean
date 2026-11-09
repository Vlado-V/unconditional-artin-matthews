module

public import ArtinMatthews.MarkedRepresentedDivisors
public import OAI.NumberTheory.Jacobsthal.Analysis.BonferroniDensity


set_option backward.privateInPublic true
@[expose] public section

/-!
# Positive truncation of the represented-band residual

The proved OAI Bonferroni inequalities apply to the residual factors in
both single and repeated marking arrays. The repeated-array exponent is
retained as `a=2`; it is never replaced by the single-array damping.
-/

namespace ArtinMatthews

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

noncomputable def markedResidualInput (u a : ℕ) (ρ : ℝ) (p : ℕ) : ℝ :=
  (1 - ρ ^ a) * (if p ∣ u then 1 else 0)

noncomputable def markedResidualTruncation (k : ℕ) (P S : Finset ℕ)
    (u a : ℕ) (ρ : ℝ) : ℝ :=
  BonferroniDensity.densityPolynomial k (P \ S) (markedResidualInput u a ρ)

noncomputable def markedResidualTail (k : ℕ) (P S : Finset ℕ)
    (u a : ℕ) (ρ : ℝ) : ℝ :=
  BonferroniDensity.elementarySum (P \ S) (markedResidualInput u a ρ) k

theorem markedResidualInput_bounds (u a p : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    0 ≤ markedResidualInput u a ρ p ∧ markedResidualInput u a ρ p ≤ 1 := by
  have hp0 : 0 ≤ ρ ^ a := pow_nonneg hρ0 a
  have hp1 : ρ ^ a ≤ 1 := pow_le_one₀ hρ0 hρ1
  unfold markedResidualInput
  split_ifs <;> constructor <;> simp_all

/-- The upper truncation has a pointwise nonnegative error dominated by
one positive elementary-symmetric tail. -/
theorem markedResidualTruncation_error (m : ℕ) (P S : Finset ℕ)
    (u a : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    0 ≤ markedResidualTruncation (2 * m) P S u a ρ - representedBandResidual P S u a ρ ∧
    markedResidualTruncation (2 * m) P S u a ρ - representedBandResidual P S u a ρ ≤
      markedResidualTail (2 * m + 1) P S u a ρ := by
  have hb := BonferroniDensity.densityPolynomial_bounds (P \ S) (markedResidualInput u a ρ)
    (fun p _ => (markedResidualInput_bounds u a p hρ0 hρ1).1)
    (fun p _ => (markedResidualInput_bounds u a p hρ0 hρ1).2) m
  have hg := BonferroniDensity.densityPolynomial_gap m (P \ S) (markedResidualInput u a ρ)
  change BonferroniDensity.densityPolynomial (2 * m + 1) (P \ S) (markedResidualInput u a ρ) ≤
      representedBandResidual P S u a ρ ∧
    representedBandResidual P S u a ρ ≤
      BonferroniDensity.densityPolynomial (2 * m) (P \ S) (markedResidualInput u a ρ) at hb
  unfold markedResidualTruncation markedResidualTail
  constructor <;> linarith [hb.1, hb.2]

/-- The lower truncation is no larger than the true residual. -/
theorem markedResidualTruncation_lower (m : ℕ) (P S : Finset ℕ)
    (u a : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    markedResidualTruncation (2 * m + 1) P S u a ρ ≤ representedBandResidual P S u a ρ :=
  (BonferroniDensity.densityPolynomial_bounds (P \ S) (markedResidualInput u a ρ)
    (fun p _ => (markedResidualInput_bounds u a p hρ0 hρ1).1)
    (fun p _ => (markedResidualInput_bounds u a p hρ0 hρ1).2) m).1

/-- The reciprocal-prime model mass of a positive tail has factorial decay.
This is the exact bound needed after the retained progression count. -/
theorem markedResidual_model_tail_le (P S : Finset ℕ) (a k : ℕ)
    {ρ V : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, (1 - ρ ^ a) / (p : ℝ) ≤ V) :
    BonferroniDensity.elementarySum (P \ S) (fun p => (1 - ρ ^ a) / (p : ℝ)) k ≤
      V ^ k / k.factorial := by
  apply BonferroniDensity.elementarySum_le_pow_div_factorial _ _ _ hV hmass k
  intro p _
  exact div_nonneg (sub_nonneg.mpr (pow_le_one₀ hρ0 hρ1)) (Nat.cast_nonneg _)

theorem markedResidual_model_tail_exp_le (P S : Finset ℕ) (a k : ℕ)
    {ρ V : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, (1 - ρ ^ a) / (p : ℝ) ≤ V) :
    BonferroniDensity.elementarySum (P \ S) (fun p => (1 - ρ ^ a) / (p : ℝ)) k ≤
      Real.exp (2 * V) / (2 : ℝ) ^ k := by
  apply BonferroniDensity.elementarySum_le_exponential _ _ _ hV hmass k
  intro p _
  exact div_nonneg (sub_nonneg.mpr (pow_le_one₀ hρ0 hρ1)) (Nat.cast_nonneg _)

/-- Retained subsets have an explicit divisor-level bound. -/
theorem markedResidual_divisor_level (P S : Finset ℕ) {z k : ℕ}
    (hP : ∀ p ∈ P, p ≤ z) {T : Finset ℕ} (hT : T ∈ (P \ S).powersetCard k) :
    (∏ p ∈ T, p) ≤ z ^ k := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
  calc
    (∏ p ∈ T, p) ≤ ∏ _p ∈ T, z :=
      Finset.prod_le_prod (fun p hp => hP p (Finset.mem_sdiff.mp (hsub hp)).1)
    _ = z ^ k := by simp [hcard]

end ArtinMatthews
