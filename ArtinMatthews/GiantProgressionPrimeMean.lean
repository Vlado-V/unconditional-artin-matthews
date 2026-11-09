module

public import ArtinMatthews.GiantProgressionPrimeAnnular


set_option backward.privateInPublic true
@[expose] public section

/-! Removing the logarithmic prime weight from the actual fixed-residue
smooth prime mean. All bounds use the proved residue-class PNT and its
Chebyshev estimate, with no prime-mean premise. -/
namespace ArtinMatthews
noncomputable section
open Filter ArithmeticFunction MeasureTheory
open scoped BigOperators Topology

theorem giant_unit_prime_annular_log_error_bound {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) {C K a b x : ℝ} (hC : 0≤C)
    (hbound : ∀ N : ℕ, cumsum (giantUnitPrimeLogCoeff U) N ≤ C*N)
    (hK : 0≤K) (hΦ : ∀ y∈Set.Icc a b, |Φ y|≤K)
    (ha : 0<a) (hab : a≤b) (hx : 1≤x) (hxa : 1<x*a) :
    ‖Real.log x * giantUnitPrimeAnnular U Φ a b x / x - giantUnitPrimeLogAnnular U Φ a b x / x‖ ≤
      ((|Real.log a|+|Real.log b|)*K) * (C*(b+1)/Real.log (x*a)) := by
  have hx0 : 0<x := zero_lt_one.trans_le hx
  have heq : Real.log x * giantUnitPrimeAnnular U Φ a b x - giantUnitPrimeLogAnnular U Φ a b x =
      ∑ p ∈ giantUnitAnnularPrimes U a b x, (Real.log x-Real.log p)*Φ (p/x) := by
    rw [giantUnitPrimeLogAnnular_eq]
    simp only [giantUnitPrimeAnnular, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul]
  rw [← sub_div, heq, norm_div, Real.norm_of_nonneg hx0.le]
  calc
    _ ≤ (∑ p ∈ giantUnitAnnularPrimes U a b x, ‖(Real.log x-Real.log p)*Φ (p/x)‖)/x :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) hx0.le
    _ ≤ (∑ _p ∈ giantUnitAnnularPrimes U a b x, (|Real.log a|+|Real.log b|)*K)/x := by
      apply div_le_div_of_nonneg_right _ hx0.le
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hr := giantUnitAnnularPrimes_ratio U ha.le hab hx0 hp
      exact mul_le_mul (OAI.SevenEighths.PNT.AnnularPrimeMass.log_norm_difference_bound ha hab hx0 hr)
        (hΦ _ hr) (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ((|Real.log a|+|Real.log b|)*K)*((giantUnitAnnularPrimes U a b x).card/x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (giantUnitAnnularPrimes_card_bound U hC hbound ha hab hx hxa)
      (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hK)

theorem giant_unit_prime_annular_log_error_tendsto {M : ℕ} (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    Tendsto (fun x : ℝ => Real.log x * giantUnitPrimeAnnular U Φ a b x / x -
      giantUnitPrimeLogAnnular U Φ a b x / x) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := giantUnitPrimeLogCoeff_chebyshev U
  obtain ⟨K,hKbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦ.continuousOn
  have hK : 0≤K := (norm_nonneg _).trans (hKbound a ⟨le_rfl,hab⟩)
  have hup : Tendsto (fun x : ℝ => ((|Real.log a|+|Real.log b|)*K)*
      (C*(b+1)/Real.log (x*a))) atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp (tendsto_id.atTop_mul_const ha))
    convert (hi.const_mul (C*(b+1))).const_mul ((|Real.log a|+|Real.log b|)*K) using 1 <;>
      simp only [div_eq_mul_inv, mul_zero, Function.comp_def, id_eq]
  apply squeeze_zero_norm' _ hup
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_id.atTop_mul_const ha).eventually_gt_atTop 1] with x hx hxa
  exact giant_unit_prime_annular_log_error_bound U Φ hC hbound hK
    (fun y hy => by simpa only [Real.norm_eq_abs] using hKbound y hy) ha hab hx hxa

/-- The actual smooth prime progression mean, including its exact density. -/
theorem giant_unit_prime_annular_mean {M : ℕ} [NeZero M] (U : Finset (ZMod M)ˣ)
    (Φ : ℝ → ℝ) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (hΦa : Φ a=0) (hΦb : Φ b=0) :
    Tendsto (fun x : ℝ => Real.log x * giantUnitPrimeAnnular U Φ a b x / x) atTop
      (𝓝 ((U.card : ℝ)/M.totient * ∫ t in a..b, Φ t)) := by
  have h := (giant_unit_prime_annular_log_error_tendsto U Φ hΦ.continuous ha hab).add
    (giant_unit_prime_log_annular_mean U Φ hΦ hderiv ha hab hΦa hΦb)
  simpa only [sub_add_cancel, zero_add] using h

end
end ArtinMatthews
