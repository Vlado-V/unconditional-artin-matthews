module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed ramification exceptions are negligible at the prime-counting scale.
The coefficient may vary with the cutoff and may include an arbitrary bounded
residue indicator or other bounded prime weight. -/
namespace ArtinMatthews
open Filter Set
open scoped Topology BigOperators Asymptotics
noncomputable section

theorem compactPrimeTest_norm_bound (Φ : ℝ → ℂ) (hΦ : Continuous Φ)
    (hc : HasCompactSupport Φ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖Φ t‖ ≤ C := by
  obtain ⟨C,hC⟩ := ((hc.isCompact_range hΦ).image continuous_norm).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  apply (hC ?_).trans (le_max_left _ _)
  exact ⟨Φ t, ⟨t,rfl⟩, rfl⟩

theorem fixedFiniteException_normalized_norm_tendsto {ι : Type*}
    (E : Finset ι) (F : ℝ → ι → ℂ) (C : ι → ℝ)
    (hF : ∀ᶠ x : ℝ in atTop, ∀ n ∈ E, ‖F x n‖ ≤ C n) :
    Tendsto (fun x : ℝ => Real.log x / x * ‖∑ n ∈ E, F x n‖) atTop (𝓝 0) := by
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.mul_const (∑ n ∈ E, C n)
  simp only [id_eq, zero_mul] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact mul_nonneg (div_nonneg (Real.log_pos hx).le (by linarith)) (norm_nonneg _)
  · filter_upwards [hF, eventually_gt_atTop (1:ℝ)] with x hfx hx
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.log_pos hx).le (by linarith))
    exact (norm_sum_le E (fun n => F x n)).trans (Finset.sum_le_sum (fun n hn => hfx n hn))

theorem fixedFiniteException_isLittleO {ι : Type*}
    (E : Finset ι) (F : ℝ → ι → ℂ) (C : ι → ℝ)
    (hF : ∀ᶠ x : ℝ in atTop, ∀ n ∈ E, ‖F x n‖ ≤ C n) :
    (fun x : ℝ => ∑ n ∈ E, F x n) =o[atTop] (fun x : ℝ => x / Real.log x) := by
  apply Asymptotics.isLittleO_norm_left.mp
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact fun hz => (div_pos (by linarith : 0 < x) (Real.log_pos hx)).ne' hz |>.elim
  · apply (fixedFiniteException_normalized_norm_tendsto E F C hF).congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    field_simp

/-- In particular, deleting any fixed set of ramified primes costs
`o(x/log x)` for the literal shifted smooth test and a bounded prime weight. -/
theorem smooth_fixed_prime_exception_isLittleO (E : Finset ℕ)
    (Φ : ℝ → ℂ) (hΦ : Continuous Φ) (hc : HasCompactSupport Φ)
    (a : ℝ → ℕ → ℂ) (ha : ∀ x p, p ∈ E → ‖a x p‖ ≤ 1) :
    (fun x : ℝ => ∑ p ∈ E, Φ (((p:ℝ)-1)/x) * a x p)
      =o[atTop] (fun x : ℝ => x / Real.log x) := by
  obtain ⟨C,hC,hbound⟩ := compactPrimeTest_norm_bound Φ hΦ hc
  apply fixedFiniteException_isLittleO E _ (fun _ => C)
  apply Filter.Eventually.of_forall
  intro x p hp
  rw [norm_mul]
  exact (mul_le_mul (hbound _) (ha x p hp) (norm_nonneg _) hC).trans_eq (mul_one C)

/-- The fixed exceptional set can be intersected with any cutoff-dependent
prime range without changing the conclusion. -/
theorem smooth_fixed_prime_exception_mask_isLittleO (E : Finset ℕ)
    (P : ℝ → Finset ℕ) (Φ : ℝ → ℂ) (hΦ : Continuous Φ) (hc : HasCompactSupport Φ)
    (a : ℝ → ℕ → ℂ) (ha : ∀ x p, p ∈ E → ‖a x p‖ ≤ 1) :
    (fun x : ℝ => ∑ p ∈ E, if p ∈ P x then Φ (((p:ℝ)-1)/x) * a x p else 0)
      =o[atTop] (fun x : ℝ => x / Real.log x) := by
  classical
  have h := smooth_fixed_prime_exception_isLittleO E Φ hΦ hc
    (fun x p => if p ∈ P x then a x p else 0) (by
      intro x p hp
      split_ifs
      · exact ha x p hp
      · simp)
  simpa only [mul_ite, mul_zero] using h

/-- Exact deletion of the fixed exceptional primes from a varying finite
prime range changes the literal shifted smooth sum by a negligible term. -/
theorem smooth_prime_sum_delete_fixed_isLittleO (E : Finset ℕ)
    (P : ℝ → Finset ℕ) (Φ : ℝ → ℂ) (hΦ : Continuous Φ) (hc : HasCompactSupport Φ)
    (a : ℝ → ℕ → ℂ) (ha : ∀ x p, p ∈ E → ‖a x p‖ ≤ 1) :
    (fun x : ℝ => (∑ p ∈ P x, Φ (((p:ℝ)-1)/x) * a x p) -
      ∑ p ∈ P x \ E, Φ (((p:ℝ)-1)/x) * a x p)
      =o[atTop] (fun x : ℝ => x / Real.log x) := by
  classical
  have h := smooth_fixed_prime_exception_mask_isLittleO E P Φ hΦ hc a ha
  apply h.congr' _ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [Finset.sum_ite_mem, Finset.inter_comm]
  have hs := Finset.sum_inter_add_sum_sdiff (P x) E
    (fun p => Φ (((p:ℝ)-1)/x) * a x p)
  exact eq_sub_iff_add_eq.mpr hs

end
end ArtinMatthews
