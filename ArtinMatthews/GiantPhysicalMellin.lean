module

public import ArtinMatthews.PrimeExtractionMellinBilinear
public import ArtinMatthews.PrimeExtractionSeparatedCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Mellin separation on finite physical edges. The edge dilation remains
inside the finite sum, with its negative frequency and exact Fourier convention. -/
namespace ArtinMatthews
open Filter MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap ContDiff ComplexConjugate
noncomputable section

theorem giantPhysicalMellinPhase_div (t : ℝ) {n x D : ℝ}
    (hn : 0 < n) (hx : 0 < x) (hD : 0 < D) :
    primeExtractionMellinPhase t (n / (x * D)) =
      primeExtractionMellinPhase t n * primeExtractionMellinPhase (-t) x *
        primeExtractionMellinPhase (-t) D := by
  unfold primeExtractionMellinPhase
  rw [Real.log_div hn.ne' (mul_ne_zero hx.ne' hD.ne'), Real.log_mul hx.ne' hD.ne']
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem giantPhysicalMellinPhase_conj (t n : ℝ) :
    star (primeExtractionMellinPhase t n) = primeExtractionMellinPhase (-t) n := by
  simp only [Complex.star_def]
  unfold primeExtractionMellinPhase
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem giantPhysicalMellinPhase_nat_cpow (t : ℝ) {D : ℕ} (hD : 0 < D) :
    primeExtractionMellinPhase t D = (D : ℂ) ^ (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  rw [primeExtractionMellinPhase_eq_markedLogTwist, markedLogTwist_eq_cpow hD]
  rw [mul_comm Complex.I]

def giantPhysicalMellinSum {ι : Type*} (edges : Finset ι)
    (A : ι → ℂ) (position dilation : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ e ∈ edges, A e * primeExtractionMellinPhase t (position e) *
    primeExtractionMellinPhase (-t) (dilation e)

theorem giantPhysicalMellinSum_norm_le {ι : Type*} (edges : Finset ι)
    (A : ι → ℂ) (position dilation : ι → ℝ) (t : ℝ) :
    ‖giantPhysicalMellinSum edges A position dilation t‖ ≤ ∑ e ∈ edges, ‖A e‖ := by
  unfold giantPhysicalMellinSum
  apply (norm_sum_le _ _).trans_eq
  simp only [norm_mul, primeExtractionMellinPhase_norm, mul_one]

theorem giantPhysicalMellin_integrable {ι : Type*} (edges : Finset ι)
    (A : ι → ℂ) (position dilation : ι → ℝ) (F : SchwartzMap ℝ ℂ)
    {x : ℝ} (hx : 0 < x) (hn : ∀ e ∈ edges, 0 < position e)
    (hD : ∀ e ∈ edges, 0 < dilation e) :
    Integrable (fun t : ℝ => F t * primeExtractionMellinPhase (-t) x *
      giantPhysicalMellinSum edges A position dilation t) := by
  have hi : Integrable (fun t : ℝ => ∑ e ∈ edges,
      A e * (F t * primeExtractionMellinPhase t (position e / (x * dilation e)))) :=
    integrable_finsetSum edges (fun e _ =>
      (primeExtraction_mellin_integrand_integrable F _).const_mul (A e))
  apply hi.congr
  filter_upwards [] with t
  unfold giantPhysicalMellinSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [giantPhysicalMellinPhase_div t (hn e he) hx (hD e he)]
  ring

theorem giantPhysicalMellin_setIntegral {ι : Type*} (edges : Finset ι)
    (A : ι → ℂ) (position dilation : ι → ℝ) (F : SchwartzMap ℝ ℂ)
    (S : Set ℝ) {x : ℝ} (hx : 0 < x) (hn : ∀ e ∈ edges, 0 < position e)
    (hD : ∀ e ∈ edges, 0 < dilation e) :
    (∑ e ∈ edges, A e * (∫ t : ℝ in S,
      F t * primeExtractionMellinPhase t (position e / (x * dilation e)))) =
      ∫ t : ℝ in S, F t * primeExtractionMellinPhase (-t) x *
        giantPhysicalMellinSum edges A position dilation t := by
  calc
    _ = ∑ e ∈ edges, ∫ t : ℝ in S,
        A e * (F t * primeExtractionMellinPhase t (position e / (x * dilation e))) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [integral_const_mul]
    _ = ∫ t : ℝ in S, ∑ e ∈ edges,
        A e * (F t * primeExtractionMellinPhase t (position e / (x * dilation e))) := by
      rw [integral_finsetSum edges (fun e _ =>
        ((primeExtraction_mellin_integrand_integrable F _).const_mul (A e)).integrableOn)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      unfold giantPhysicalMellinSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [giantPhysicalMellinPhase_div t (hn e he) hx (hD e he)]
      ring

theorem giantPhysicalMellin_cutoff {ι : Type*} (edges : Finset ι)
    (A : ι → ℂ) (position dilation : ι → ℝ) (Ψ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Ψ ⊆ Set.Icc a b) (hΨ : ContDiff ℝ ∞ Ψ)
    {x : ℝ} (hx : 0 < x) (hn : ∀ e ∈ edges, 0 < position e)
    (hD : ∀ e ∈ edges, 0 < dilation e) :
    (∑ e ∈ edges, A e * Ψ (position e / (x * dilation e))) =
      ∫ t : ℝ, (𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) t *
        primeExtractionMellinPhase (-t) x * giantPhysicalMellinSum edges A position dilation t := by
  calc
    _ = ∑ e ∈ edges, A e * (∫ t : ℝ in Set.univ,
        (𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) t *
          primeExtractionMellinPhase t (position e / (x * dilation e))) := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [Measure.restrict_univ]
      rw [primeExtraction_mellin_inversion Ψ ha hsupp hΨ (div_pos (hn e he) (mul_pos hx (hD e he)))]
    _ = _ := by
      simpa only [Measure.restrict_univ] using giantPhysicalMellin_setIntegral edges A position dilation
        (𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) Set.univ hx hn hD

theorem giantPhysicalMellin_cutoff_truncation {ι : Type*} (edges : Finset ι)
    (A : ι → ℂ) (position dilation : ι → ℝ) (Ψ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Ψ ⊆ Set.Icc a b) (hΨ : ContDiff ℝ ∞ Ψ)
    {x H : ℝ} (hx : 0 < x) (hH : 0 < H) (k : ℕ)
    (hn : ∀ e ∈ edges, 0 < position e) (hD : ∀ e ∈ edges, 0 < dilation e) :
    ‖(∑ e ∈ edges, A e * Ψ (position e / (x * dilation e))) -
      ∫ t : ℝ in Set.Icc (-H) H, (𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) t *
        primeExtractionMellinPhase (-t) x * giantPhysicalMellinSum edges A position dilation t‖ ≤
      ((∫ t : ℝ, |t| ^ k * ‖(𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) t‖) / H ^ k) *
        ∑ e ∈ edges, ‖A e‖ := by
  rw [← giantPhysicalMellin_setIntegral edges A position dilation
    (𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) (Set.Icc (-H) H) hx hn hD]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  rw [← mul_sub, norm_mul]
  rw [mul_comm ‖A e‖]
  exact mul_le_mul_of_nonneg_right
    (primeExtraction_mellin_truncation Ψ ha hsupp hΨ k hH
      (div_pos (hn e he) (mul_pos hx (hD e he)))) (norm_nonneg _)

end
end ArtinMatthews
