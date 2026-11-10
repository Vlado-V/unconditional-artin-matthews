module

public import ArtinMatthews.SourceComparisonFreeHit
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Finite union over the actual indexed auxiliary slots. Repetitions
are allowed in the label map and contribute their stated finite cost. -/

namespace ArtinMatthews
open Finset Set
open scoped BigOperators
noncomputable section

def sourceComparisonAuxHitRows {ι : Type*} (T : Finset ℕ) (I : Finset ι)
    (p : ι → ℕ) (d : ℕ) : Finset ℕ := by
  classical
  exact T.filter (fun w => ∃ i ∈ I, p i ∣ w ∨ p i ∣ w + d)

theorem mem_sourceComparisonAuxHitRows {ι : Type*} (T : Finset ℕ) (I : Finset ι)
    (p : ι → ℕ) (d w : ℕ) :
    w ∈ sourceComparisonAuxHitRows T I p d ↔ w ∈ T ∧ ∃ i ∈ I, p i ∣ w ∨ p i ∣ w + d := by
  classical
  exact Finset.mem_filter

theorem sourceComparison_freeHit_union_le {ι : Type*} (Ψ : ℝ → ℂ) (U V : ℕ → ℂ)
    {Y a b B : ℝ} (hY : 0 < Y) (ha : 0 < a) (hb : 0 ≤ b)
    (hΨ : ∀ x ∉ Set.Icc a b, Ψ x = 0) (hB : ∀ x, ‖Ψ x‖ ≤ B)
    (d : ℕ) (I : Finset ι) (p : ι → ℕ) (hp : ∀ i ∈ I, 0 < p i) (hpd : ∀ i ∈ I, p i ∣ d)
    {T : Finset ℕ} (hT : T ⊆ Finset.Ioc 0 ⌊b * Y⌋₊) :
    (∑ w ∈ sourceComparisonAuxHitRows T I p d, sourceComparisonFreeHitWeight Ψ U V Y d w) ≤
      (B * Real.sqrt b / a) * Y ^ (-(1 / 2 : ℝ)) *
        (sourceComparisonFourthMass ⌊b * Y⌋₊ U) ^ (1 / 4 : ℝ) *
        (sourceComparisonFourthMass ⌊b * Y + (d : ℝ)⌋₊ V) ^ (1 / 4 : ℝ) *
        ∑ i ∈ I, (p i : ℝ) ^ (-(1 / 2 : ℝ)) := by
  classical
  let f := sourceComparisonFreeHitWeight Ψ U V Y d
  let Q (i : ι) (w : ℕ) := p i ∣ w ∨ p i ∣ w + d
  let C := (B * Real.sqrt b / a) * Y ^ (-(1 / 2 : ℝ)) *
    (sourceComparisonFourthMass ⌊b * Y⌋₊ U) ^ (1 / 4 : ℝ) *
    (sourceComparisonFourthMass ⌊b * Y + (d : ℝ)⌋₊ V) ^ (1 / 4 : ℝ)
  have hf (w : ℕ) : 0 ≤ f w := sourceComparisonFreeHitWeight_nonneg Ψ U V Y d w
  change (∑ w ∈ sourceComparisonAuxHitRows T I p d, f w) ≤ C * _
  calc
    _ = ∑ w ∈ T, if ∃ i ∈ I, Q i w then f w else 0 := by
      unfold sourceComparisonAuxHitRows
      rw [Finset.sum_filter]
    _ ≤ ∑ w ∈ T, ∑ i ∈ I, if Q i w then f w else 0 := by
      apply Finset.sum_le_sum
      intro w _
      have hnn (i : ι) : 0 ≤ if Q i w then f w else 0 := ite_nonneg (hf w) le_rfl
      by_cases he : ∃ i ∈ I, Q i w
      · obtain ⟨i, hi, hQ⟩ := he
        have h := Finset.single_le_sum (f := fun j => if Q j w then f w else 0) (fun j _ => hnn j) hi
        rw [if_pos hQ] at h
        rw [if_pos ⟨i, hi, hQ⟩]
        exact h
      · rw [if_neg he]
        exact Finset.sum_nonneg fun i _ => hnn i
    _ = ∑ i ∈ I, ∑ w ∈ T.filter (Q i), f w := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_filter]
    _ ≤ ∑ i ∈ I, C * (p i : ℝ) ^ (-(1 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have he := sourceComparison_freeHit_le_of_subset Ψ U V hY ha hb hΨ hB d (p i) (hp i hi) (hpd i hi) hT
      change (∑ w ∈ T.filter (fun w => p i ∣ w ∨ p i ∣ w + d), f w) ≤ _ at he
      refine he.trans_eq ?_
      dsimp only [C]
      ring
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem sourceComparison_freeHit_union_le_of_lower {ι : Type*} (Ψ : ℝ → ℂ) (U V : ℕ → ℂ)
    {Y a b B : ℝ} (hY : 0 < Y) (ha : 0 < a) (hb : 0 ≤ b)
    (hΨ : ∀ x ∉ Set.Icc a b, Ψ x = 0) (hB : ∀ x, ‖Ψ x‖ ≤ B)
    (d : ℕ) (I : Finset ι) (p : ι → ℕ) {Q : ℝ} (hQ : 0 < Q)
    (hlo : ∀ i ∈ I, Q ≤ (p i : ℝ)) (hpd : ∀ i ∈ I, p i ∣ d)
    {T : Finset ℕ} (hT : T ⊆ Finset.Ioc 0 ⌊b * Y⌋₊) :
    (∑ w ∈ sourceComparisonAuxHitRows T I p d, sourceComparisonFreeHitWeight Ψ U V Y d w) ≤
      (B * Real.sqrt b / a) * Y ^ (-(1 / 2 : ℝ)) *
        (sourceComparisonFourthMass ⌊b * Y⌋₊ U) ^ (1 / 4 : ℝ) *
        (sourceComparisonFourthMass ⌊b * Y + (d : ℝ)⌋₊ V) ^ (1 / 4 : ℝ) *
        ((I.card : ℝ) * Q ^ (-(1 / 2 : ℝ))) := by
  have hp (i : ι) (hi : i ∈ I) : 0 < p i := by exact_mod_cast hQ.trans_le (hlo i hi)
  refine (sourceComparison_freeHit_union_le Ψ U V hY ha hb hΨ hB d I p hp hpd hT).trans ?_
  have hB₀ : 0 ≤ B := (norm_nonneg (Ψ 0)).trans (hB 0)
  have hU₀ : 0 ≤ sourceComparisonFourthMass ⌊b * Y⌋₊ U :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hV₀ : 0 ≤ sourceComparisonFourthMass ⌊b * Y + (d : ℝ)⌋₊ V :=
    Finset.sum_nonneg fun _ _ => by positivity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ i ∈ I, (p i : ℝ) ^ (-(1 / 2 : ℝ))) ≤ ∑ _ ∈ I, Q ^ (-(1 / 2 : ℝ)) :=
      Finset.sum_le_sum fun i hi => Real.rpow_le_rpow_of_nonpos hQ (hlo i hi) (by norm_num)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end
end ArtinMatthews
