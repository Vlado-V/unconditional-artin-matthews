module

public import ArtinMatthews.ShiftedVoronoiMellinSummation
public import ArtinMatthews.ShiftedVoronoiAdditiveContinuation


set_option backward.privateInPublic true
@[expose] public section

/-!
# The source coefficient sum as an absolutely convergent Mellin integral

This specializes OAI's sum–integral argument to actual cusp-form coefficients.
The source's smooth compact support supplies Mellin inversion and vertical
integrability, and the cusp-form mean square supplies coefficient summability.
-/

noncomputable section
open Complex UpperHalfPlane MeasureTheory Set Filter
open OAI.CubicReflectionKernel
open scoped Topology ContDiff

namespace ArtinMatthews

/-- Smooth compact sources away from zero have integrable vertical Mellin lines. -/
theorem compact_mellin_vertical_integrable
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (a b : ℝ) (ha : 0 < a)
    (hHs : Function.support H ⊆ Icc a b) (σ : ℝ) :
    Integrable (fun t : ℝ ↦ mellin H ((σ : ℂ) + t * Complex.I)) := by
  obtain ⟨C, _, hb⟩ := compact_source_mellin_strip_decay H a b ha hHs hH σ σ 2
  have hc : Continuous (fun t : ℝ ↦ mellin H ((σ : ℂ) + t * Complex.I)) :=
    (compact_source_mellin_differentiable H a b ha hHs hH).continuous.comp (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    simpa only [div_eq_mul_inv] using weighted_two_to_cauchy (norm_nonneg _) t
      (hb σ ⟨le_rfl, le_rfl⟩ t)

/-- Source Mellin inversion with all analytic premises supplied by the source. -/
theorem compact_mellin_inversion
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (a b : ℝ) (ha : 0 < a)
    (hHs : Function.support H ⊆ Icc a b) (σ x : ℝ) (hx : 0 < x) :
    mellinInv σ (mellin H) x = H x :=
  mellinInv_mellin_eq σ H hx (compact_source_mellin_convergent H a b ha hHs hH σ)
    (compact_mellin_vertical_integrable H hH a b ha hHs σ) hH.continuous.continuousAt

/-- Absolute coefficient summability on the positive integer index set. -/
theorem cuspAdditiveCoeff_summable_natSucc
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (x σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ ↦ ‖cuspAdditiveCoeff f x (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ (-σ)) := by
  have hs := (weightOne_additiveCoeff_LSeriesSummable f hperiod x (σ : ℂ)
    (by simpa using hσ)).norm
  have hshift := (summable_nat_add_iff 1).mpr hs
  simpa only [LSeries.norm_term_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ite_false, Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv] using hshift

/-- The positive-index power series agrees with the usual L-series. -/
theorem cuspAdditiveCoeff_tsum_natSucc
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (x : ℝ) (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, cuspAdditiveCoeff f x (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-s)) =
      LSeries (cuspAdditiveCoeff f x) s := by
  have h := (weightOne_additiveCoeff_LSeriesSummable f hperiod x s hs).tsum_eq_zero_add
  rw [LSeries.term_zero, zero_add] at h
  simpa only [LSeries, LSeries.term_def₀ (cuspAdditiveCoeff_zero f hperiod x)] using h.symm

set_option maxHeartbeats 800000 in
/-- The actual smoothed coefficient sum is the right-line Mellin integral.
No convergence or Mellin identity is assumed of the coefficients. -/
theorem weightOne_source_sum_mellin
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (x : ℝ) (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H)
    (a b : ℝ) (ha : 0 < a) (hHs : Function.support H ⊆ Icc a b)
    (σ Z : ℝ) (hσ : 1 < σ) (hZ : 0 < Z) :
    HasSum (fun n : ℕ ↦ cuspAdditiveCoeff f x n * H ((n : ℝ) / Z))
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        mellin H ((σ : ℂ) + t * Complex.I) * (Z : ℂ) ^ ((σ : ℂ) + t * Complex.I) *
          cuspAdditiveL f x ((σ : ℂ) + t * Complex.I)) := by
  have hi := hasSum_mellinInv_scaled (fun n : ℕ ↦ cuspAdditiveCoeff f x (n + 1))
    (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) (fun n ↦ by positivity) (mellin H) σ
    (compact_mellin_vertical_integrable H hH a b ha hHs σ)
    (cuspAdditiveCoeff_summable_natSucc f hperiod x σ hσ) Z hZ
  have hterms (n : ℕ) : mellinInv σ (mellin H) (((n + 1 : ℕ) : ℝ) / Z) =
      H (((n + 1 : ℕ) : ℝ) / Z) :=
    compact_mellin_inversion H hH a b ha hHs σ _ (by positivity)
  simp only [hterms] at hi
  have hseries (t : ℝ) : (∑' n : ℕ, cuspAdditiveCoeff f x (n + 1) *
      (((n + 1 : ℕ) : ℝ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I))) =
      cuspAdditiveL f x ((σ : ℂ) + t * Complex.I) := by
    rw [cuspAdditiveL_eq_LSeries f hperiod _ _ (by simpa using hσ)]
    simpa only [Complex.ofReal_natCast] using
      cuspAdditiveCoeff_tsum_natSucc f hperiod x _ (by simpa using hσ)
  simp only [hseries] at hi
  have hall := (hasSum_nat_add_iff (f := fun n : ℕ ↦ cuspAdditiveCoeff f x n * H ((n : ℝ) / Z)) 1).mp hi
  simpa only [Finset.sum_range_one, cuspAdditiveCoeff_zero f hperiod x,
    zero_mul, add_zero] using hall

end ArtinMatthews
