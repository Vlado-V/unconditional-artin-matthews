module

public import ArtinMatthews.ProbeBadPrimeSeries
public import Mathlib.Analysis.Normed.Module.FiniteDimension


set_option backward.privateInPublic true
@[expose] public section

/-! The untruncated local e,l,k,m series: absolute convergence and its
equality with the two surviving outer-modulus terms. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def probeBadPrimeOriginalSeries (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (j : ℕ) (a b W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' i : ℕ × (ℕ × ℕ),
    probeBadPrimeWeight K p hp χ j a b W V e i.2.1 i.1 i.2.2

theorem probeBadPrimeOriginal_norm_summable (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm (Ideal.span {p})) b < 1) (hV : ‖V‖ < 1)
    (e : Fin 2) :
    Summable (fun i : ℕ × (ℕ × ℕ) =>
      ‖probeBadPrimeWeight K p hp.ne_zero χ j a b W V e i.2.1 i.1 i.2.2‖) := by
  have hz (k : ℕ) (hk : k ∉ ({0, 1} : Finset ℕ)) (v : ℕ × ℕ) :
      probeBadPrimeWeight K p hp.ne_zero χ j a b W V e v.1 k v.2 = 0 := by
    have hk2 : 2 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk2
    simpa only [Nat.add_comm] using probeBadPrimeWeight_higher_zero K p hp χ j hj a b W V e v.1 r v.2
  have hi (k : ℕ) : Summable (fun v : ℕ × ℕ =>
      ‖probeBadPrimeWeight K p hp.ne_zero χ j a b W V e v.1 k v.2‖) := by
    by_cases h0 : k = 0
    · subst k
      simpa only [probeBadPrimePair, Fin.val_zero, add_zero] using
        (probeBadPrimePair_summable K p hp χ hχ hminus j a b W V hA hV e 0 0).norm
    by_cases h1 : k = 1
    · subst k
      simpa only [probeBadPrimePair, Fin.val_one, add_zero] using
        (probeBadPrimePair_summable K p hp χ hχ hminus j a b W V hA hV e 1 0).norm
    · have hk : k ∉ ({0, 1} : Finset ℕ) := by simp [h0, h1]
      simpa only [hz k hk, norm_zero] using (summable_zero : Summable (fun _ : ℕ × ℕ => (0 : ℝ)))
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨hi, ?_⟩
  apply summable_of_ne_finset_zero (s := {0, 1})
  intro k hk
  simp only [hz k hk, norm_zero, tsum_zero]

theorem probeBadPrimeOriginalSeries_eq (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (j : ℕ) (hj : 0 < j) (a b W V : ℂ)
    (hA : probeBadA (Ideal.absNorm (Ideal.span {p})) b < 1) (hV : ‖V‖ < 1) :
    probeBadPrimeOriginalSeries K p hp.ne_zero χ j a b W V =
      probeBadPrimeLocalSeries K p hp.ne_zero χ j a b W V := by
  unfold probeBadPrimeOriginalSeries probeBadPrimeLocalSeries
  apply Finset.sum_congr rfl
  intro e _
  rw [(probeBadPrimeOriginal_norm_summable K p hp χ hχ hminus j hj a b W V hA hV e).of_norm.tsum_prod]
  rw [tsum_eq_sum (s := ({0, 1} : Finset ℕ)) (fun k hk => by
    have hk2 : 2 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk2
    simp only [show ∀ v : ℕ × ℕ,
      probeBadPrimeWeight K p hp.ne_zero χ j a b W V e v.1 (2 + r) v.2 = 0 from
      fun v => by simpa only [Nat.add_comm] using
        probeBadPrimeWeight_higher_zero K p hp χ j hj a b W V e v.1 r v.2, tsum_zero])]
  simp only [Fin.sum_univ_two, Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, Nat.zero_ne_one, not_false_eq_true, Fin.val_zero, Fin.val_one,
    probeBadPrimePair, add_zero]

end
end ArtinMatthews.VaryingKummerAnalytic
