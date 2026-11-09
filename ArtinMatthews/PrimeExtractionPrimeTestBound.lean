module

public import ArtinMatthews.PrimeExtractionPrimeTestIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine long-frequency character tests for the literal extracted
prime coefficient. The rough cutoff and retained Mellin frequency remain
explicit and uniform. -/

noncomputable section
namespace ArtinMatthews
open OAI.SevenEighths Filter
open scoped BigOperators Classical

theorem primeExtractionFirstPhaseCoefficient_all_log (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (A₀ B δ D R : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (ϑ : DirichletCharacter ℂ q) (H : ℝ), x^δ ≤ H →
      ∀ m n : ℕ, m ≤ n → H ≤ m → (n : ℝ) ≤ 2*H →
      ∀ z : ℝ, 0 ≤ z → ∀ v t : ℝ, |v| ≤ (Real.log x)^R → |t| ≤ x^B →
      ‖markedTwistedSum (Finset.Icc m n)
        (primeExtractionFirstPhaseCoefficient (cubicNumeratorHeckeCharacter A hA) χ z v)
        ϑ t‖ ≤ 35*H*(Real.log x)^(-D) := by
  filter_upwards [cubicNumeratorPrimeInterval_fixed_twist_all_log A hA hnoncube χ
      A₀ (B+2) δ D (by linarith) hδ hD,
    primeExtraction_retained_frequency_bound B R hB,
    eventually_gt_atTop (1 : ℝ)] with x hprime hfreq hx
  intro q _ hq ϑ H hH m n _ hmH hnH z hz v t hv ht
  rw [primeExtractionFirstPhaseCoefficient_interval_test _ χ ϑ hz v t m n]
  by_cases hmn : max m (⌊z⌋₊+1) ≤ n
  · exact hprime q hq ϑ H hH _ n hmn
      (hmH.trans (by exact_mod_cast le_max_left m (⌊z⌋₊+1))) hnH
      _ (hfreq t v ht hv)
  · have hempty : Finset.Icc (max m (⌊z⌋₊+1)) n = ∅ := Finset.Icc_eq_empty hmn
    rw [hempty]
    simp only [Finset.filter_empty, Finset.sum_empty, norm_zero]
    have hHpos : 0 < H := (Real.rpow_pos_of_pos (by linarith : 0 < x) δ).trans_le hH
    exact mul_nonneg (mul_nonneg (by norm_num) hHpos.le)
      (Real.rpow_nonneg (Real.log_pos hx).le _)

theorem primeExtractionFirstPhaseCoefficient_normalized_all_log (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3 = (A : OAI.CubicFirstMoment.Eisenstein))
    {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (A₀ B δ D R : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log x)^A₀ →
      ∀ (ϑ : DirichletCharacter ℂ q) (H : ℝ), x^δ ≤ H →
      ∀ m n : ℕ, m ≤ n → H ≤ m → (n : ℝ) ≤ 2*H →
      ∀ z : ℝ, 0 ≤ z → ∀ v t : ℝ, |v| ≤ (Real.log x)^R → |t| ≤ x^B →
      ‖markedTwistedSum (Finset.Icc m n)
        (primeExtractionFirstPhaseCoefficient (cubicNumeratorHeckeCharacter A hA) χ z v)
        ϑ t‖ / H ≤ 35*(Real.log x)^(-D) := by
  filter_upwards [primeExtractionFirstPhaseCoefficient_all_log A hA hnoncube χ
    A₀ B δ D R hB hδ hD, eventually_gt_atTop (0 : ℝ)] with x hprime hx
  intro q _ hq ϑ H hH m n hmn hmH hnH z hz v t hv ht
  have hHpos : 0 < H := (Real.rpow_pos_of_pos hx δ).trans_le hH
  apply (div_le_iff₀ hHpos).mpr
  exact (hprime q hq ϑ H hH m n hmn hmH hnH z hz v t hv ht).trans_eq (by ring)

end ArtinMatthews
