module

public import ArtinMatthews.GiantSignedCappedBoundaryRank
public import ArtinMatthews.GiantSignedBirthMixedBoundary
public import ArtinMatthews.MarkedBirthRankNormSplit
public import Mathlib.Data.Fintype.Perm


set_option backward.privateInPublic true
@[expose] public section

/-! The actual unrestricted distinct-birth boundary combines the
signed capped permutation expansion with the original cap error. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
universe u

local instance sourceDistinctRankPermutationFintype {B : Type*} [Fintype B] {M n H : ℕ} :
    Fintype (Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) :=
  @Equiv.instFintype (GiantSignedUniformBirthAddress B M n H)
    (GiantSignedUniformBirthAddress B M n H) inferInstance inferInstance inferInstance inferInstance

variable {S B I : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}
    [Fintype (GiantTwoSidedResidueState PS (k+ell))]

theorem giantSignedBirthDistinctBoundary_norm_of_rank_bounds
    (H : ℕ) (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (q ρ θ : ℝ)
    (n : ℕ) (patterns : Fin n → Finset I) (C : Fin n → I → B → Finset (Fin k))
    (κ : Fin n → ℤ) (visitQ : Fin (n+1) → ℝ) (ζ : Fin n → ℝ)
    (K : (i : Fin n) → (p : I) → GiantTwoSidedPatternCoefficient PB (C i p) ell)
    (r₀ : ℕ) {L E : ℝ} (hL : 3 ≤ L) (hn : 1 ≤ n) :
    let rows := giantSignedChronologicalTraceRows (PS := PS) ν V q ρ θ n patterns C κ visitQ ζ K
      (fun _ _ _ _ => 1)
    let distinct := giantSignedTraceBirthDistinctIndicator (PS := PS) ν V q ρ θ n patterns C κ visitQ ζ K
      (fun _ _ _ _ => 1)
    let full := giantSignedGuardedTraceBoundaryPairing ν rows distinct
    let capped := giantSignedGuardedTraceBoundaryPairing ν rows (fun s t =>
      if GiantSignedTraceWithin (fun z => (∑ g, z.2.2.1 g) ≤ H) rows s t then distinct s t else 0)
    let F := giantSignedCappedBirthEventBoundary (PS := PS) H ν V q ρ θ n patterns C κ visitQ ζ K
      (fun _ _ _ _ => 1)
    ‖full-capped‖ ≤ (L^(-(E+2)))^n →
    (∑ σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H),
      if giantSignedUniformBirthRank σ < r₀ then ‖F σ‖ else 0) ≤ (L^(-(E+2)))^n →
    (∑ σ : Equiv.Perm (GiantSignedUniformBirthAddress B (k+ell) n H),
      if r₀ ≤ giantSignedUniformBirthRank σ then ‖F σ‖ else 0) ≤ (L^(-(E+2)))^n →
    ‖full‖ ≤ (L^(-(E+1)))^n := by
  intro rows distinct full capped F hcap hlow hhigh
  let A := GiantSignedUniformBirthAddress B (k+ell) n H
  have hsig : capped = ∑ σ : Equiv.Perm A, ((σ.sign : ℤ) : ℂ)*F σ := by
    simpa only [giantSignedCappedDistinctTraceBoundary, giantSignedCappedBirthPermutationSum] using
      (giantSignedCappedTraceDistinctBoundary_permutation_sum ν V q ρ θ n patterns C κ visitQ ζ K
        (fun _ _ _ _ => 1) H)
  have hnorm : ‖capped‖ ≤ ∑ σ : Equiv.Perm A, ‖F σ‖ := by
    rw [hsig]
    refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl ?_)
    intro σ _
    rw [norm_mul, markedBirthPermutationSign_norm, one_mul]
  have hsplit : (∑ σ : Equiv.Perm A, ‖F σ‖) =
      (∑ σ : Equiv.Perm A, if giantSignedUniformBirthRank σ < r₀ then ‖F σ‖ else 0) +
      ∑ σ : Equiv.Perm A, if r₀ ≤ giantSignedUniformBirthRank σ then ‖F σ‖ else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases h : giantSignedUniformBirthRank σ < r₀
    · rw [ite_eq_left h, ite_eq_right (not_le_of_gt h), add_zero]
    · rw [ite_eq_right h, ite_eq_left (le_of_not_gt h), zero_add]
  have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 3).trans hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have h3 : 3 ≤ L^n := hL.trans (by simpa only [pow_one] using pow_le_pow_right₀ hL1 hn)
  have hpow : L*L^(-(E+2)) = L^(-(E+1)) := by
    calc
      _ = L^(1 : ℝ)*L^(-(E+2)) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hL0]; congr 1; ring
  calc
    ‖full‖ = ‖(full-capped)+capped‖ := by rw [sub_add_cancel]
    _ ≤ ‖full-capped‖ + ‖capped‖ := norm_add_le _ _
    _ ≤ 3*(L^(-(E+2)))^n := by
      rw [hsplit] at hnorm
      linarith
    _ ≤ L^n*(L^(-(E+2)))^n := mul_le_mul_of_nonneg_right h3
      (pow_nonneg (Real.rpow_nonneg hL0.le _) _)
    _ = _ := by rw [← mul_pow, hpow]

end
end ArtinMatthews
