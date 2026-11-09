module

public import ArtinMatthews.SourceComparisonHighTimeTuple
public import ArtinMatthews.MarkedMajorMellinIsolationL2
public import ArtinMatthews.PrimeExtractionMellinTail
public import Mathlib.MeasureTheory.Group.MeasurableEquiv


set_option backward.privateInPublic true
@[expose] public section

/-! Exact smooth product cutoff and its energy under Mellin separation. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap ContDiff

noncomputable section

theorem sourceComparisonHighTimes_shift_energy (f : ℝ → ℂ) (hf : Continuous f)
    (T S T' S' ξ : ℝ) (hT : T+|ξ| ≤ T') (hS : S'+|ξ| ≤ S) :
    (∫ t in sourceComparisonHighTimes T S, ‖f (t+ξ)‖^2) ≤
      ∫ t in sourceComparisonHighTimes T' S', ‖f t‖^2 := by
  let e := MeasurableEquiv.addRight ξ
  let W := sourceComparisonHighTimes T S
  let W' := sourceComparisonHighTimes T' S'
  let D := e '' W
  have he : MeasurePreserving e volume volume := measurePreserving_add_right volume ξ
  have hpre : e ⁻¹' D = W := Set.preimage_image_eq _ e.injective
  have hi : IntegrableOn (fun t => ‖f t‖^2) W' :=
    (hf.norm.pow 2).integrableOn_Icc.mono_set inter_subset_left
  have hd : D ⊆ W' := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := hv
    change t+ξ ∈ W'
    refine ⟨abs_le.mp ((abs_add_le t ξ).trans (by linarith [abs_le.mpr ht.1])), ?_⟩
    have h := abs_sub (t+ξ) ξ
    rw [add_sub_cancel_right] at h
    have ht' : S ≤ |t| := ht.2
    exact (show S' ≤ |t+ξ| by linarith only [h, hS, ht'])
  have ht := e.measurableEmbedding.setIntegral_map (μ := volume) (fun t => ‖f t‖^2) D
  rw [he.map_eq, hpre] at ht
  apply ht.symm.trans_le
  exact setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (fun _ h => hd h))

private theorem mellin_phase_translate {n : ℕ} (hn : 0 < n) {Y : ℝ} (hY : 0 < Y)
    (t ξ : ℝ) :
    primeExtractionMellinPhase ξ ((n:ℝ)/Y)*markedPrimePhase n t =
      primeExtractionMellinPhase (-ξ) Y*markedPrimePhase n (t+2*Real.pi*ξ) := by
  unfold primeExtractionMellinPhase markedPrimePhase
  rw [Real.log_div (by exact_mod_cast hn.ne') hY.ne', ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sourceComparisonNaturalPolynomial_bound (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ‖markedNaturalPolynomial S c t‖ ≤ ∑ n ∈ S, ‖c n‖ := by
  unfold markedNaturalPolynomial
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul, markedPrimePhase_norm, mul_one, le_rfl])

/-- Integrate the literal smooth cutoff on a high-time window. The retained
Mellin shifts use the high-energy bound, and the omitted shifts use the
uniform translated ordinary mean square. -/
theorem sourceComparison_smoothed_energy (ψ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support ψ ⊆ Set.Icc a b) (hψ : ContDiff ℝ ∞ ψ)
    (S : Finset ℕ) (c : ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n)
    (Y T B R σ E₀ E₁ : ℝ) (hY : 0 < Y) (hR : 0 < R) (j : ℕ)
    (hmean : ∀ ξ : ℝ, (∫ t in sourceComparisonHighTimes T B,
      ‖markedNaturalPolynomial S c (t+σ+2*Real.pi*ξ)‖^2) ≤ E₀)
    (hcore : ∀ ξ ∈ Set.Icc (-R) R, (∫ t in sourceComparisonHighTimes T B,
      ‖markedNaturalPolynomial S c (t+σ+2*Real.pi*ξ)‖^2) ≤ E₁) :
    (∫ t in sourceComparisonHighTimes T B,
      ‖markedNaturalPolynomial S (fun n => c n*ψ ((n:ℝ)/Y)) (t+σ)‖^2) ≤
      2*(∫ ξ : ℝ, ‖(𝓕 (primeExtractionLogProfile ψ ha hsupp hψ)) ξ‖)^2*E₁ +
        2*((∫ ξ : ℝ, |ξ|^j * ‖(𝓕 (primeExtractionLogProfile ψ ha hsupp hψ)) ξ‖)/R^j)^2*E₀ := by
  let W := sourceComparisonHighTimes T B
  let I := Set.Icc (-R) R
  let F₀ : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionLogProfile ψ ha hsupp hψ)
  let F : ℝ → ℂ := fun ξ => F₀ ξ*primeExtractionMellinPhase (-ξ) Y
  let A : ℝ → ℝ → ℂ := fun ξ t => markedNaturalPolynomial S c (t+σ+2*Real.pi*ξ)
  let ν := volume.restrict W
  letI : IsFiniteMeasure ν := ⟨by
    dsimp [ν]
    rw [Measure.restrict_apply_univ]
    exact (measure_mono (show W ⊆ Set.Icc (-T) T from inter_subset_left)).trans_lt
      isCompact_Icc.measure_lt_top⟩
  have hFcont : Continuous F := F₀.continuous.mul
    ((primeExtractionMellinPhase_continuous Y).comp continuous_neg)
  have hFnorm (ξ : ℝ) : ‖F ξ‖ = ‖F₀ ξ‖ := by
    simp only [F, norm_mul, primeExtractionMellinPhase_norm, mul_one]
  have hF : Integrable F := F₀.integrable.norm.mono' hFcont.aestronglyMeasurable
    (Eventually.of_forall (fun ξ => (hFnorm ξ).le))
  have hA : Continuous (fun p : ℝ × ℝ => A p.1 p.2) := by
    apply (markedNaturalPolynomial_continuous S c).comp
    change Continuous (fun p : ℝ × ℝ => p.2+σ+2*Real.pi*p.1)
    fun_prop
  have hAb (ξ t : ℝ) : ‖A ξ t‖ ≤ ∑ n ∈ S, ‖c n‖ :=
    sourceComparisonNaturalPolynomial_bound S c _
  have hI : MeasurableSet I := measurableSet_Icc
  have hcut (t : ℝ) :
      markedNaturalPolynomial S (fun n => c n*ψ ((n:ℝ)/Y)) (t+σ) =
        ∫ ξ, F ξ*A ξ t := by
    unfold A markedNaturalPolynomial
    simp_rw [mul_sum]
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro n hn
      have he (ξ : ℝ) : F ξ*(c n*markedPrimePhase n (t+σ+2*Real.pi*ξ)) =
          (c n*markedPrimePhase n (t+σ))*(F₀ ξ*primeExtractionMellinPhase ξ ((n:ℝ)/Y)) := by
        dsimp [F]
        calc
          _ = (F₀ ξ*c n)*(primeExtractionMellinPhase (-ξ) Y*
              markedPrimePhase n (t+σ+2*Real.pi*ξ)) := by ring
          _ = _ := by rw [← mellin_phase_translate (hS n hn) hY (t+σ) ξ]; ring
      simp_rw [he]
      rw [integral_const_mul, primeExtraction_mellin_inversion ψ ha hsupp hψ
        (div_pos (by exact_mod_cast hS n hn) hY)]
      ring
    · intro n _
      apply hF.mul_bdd (c := ‖c n‖)
      · have hc : Continuous (fun ξ : ℝ => c n*markedPrimePhase n (t+σ+2*Real.pi*ξ)) := by
          unfold markedPrimePhase
          fun_prop
        exact hc.aestronglyMeasurable
      · exact Eventually.of_forall (fun ξ => by simp only [norm_mul, markedPrimePhase_norm, mul_one, le_rfl])
  have hInt (t : ℝ) : Integrable (fun ξ => F ξ*A ξ t) := by
    apply hF.mul_bdd
    · exact (hA.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall (fun ξ => hAb ξ t)
  obtain ⟨hi, hcoreBound⟩ := markedMellinIsolation_weighted_L2_of_bounded
    (volume.restrict I) ν F A hF.integrableOn hA.aestronglyMeasurable
    (Eventually.of_forall (fun p => hAb p.1 p.2))
    (by filter_upwards [ae_restrict_mem hI] with ξ hξ; exact hcore ξ hξ)
  obtain ⟨hj, htailBound⟩ := markedMellinIsolation_weighted_L2_of_bounded
    (volume.restrict Iᶜ) ν F A hF.integrableOn hA.aestronglyMeasurable
    (Eventually.of_forall (fun p => hAb p.1 p.2))
    (Eventually.of_forall hmean)
  have hmass : (∫ ξ in I, ‖F ξ‖) ≤ ∫ ξ : ℝ, ‖F₀ ξ‖ := by
    simp_rw [hFnorm]
    exact setIntegral_le_integral F₀.integrable.norm
      (Eventually.of_forall (fun _ => norm_nonneg _))
  have hset : Iᶜ = {t : ℝ | R < |t|} := by
    ext t
    change (¬ t ∈ Set.Icc (-R) R) ↔ R < |t|
    rw [← not_le, abs_le]
    rfl
  have htailMass : (∫ ξ in Iᶜ, ‖F ξ‖) ≤ (∫ ξ : ℝ, |ξ|^j * ‖F₀ ξ‖)/R^j := by
    simp_rw [hFnorm]
    rw [hset]
    exact prime_extraction_schwartz_tail F₀ j hR
  have hE₀ : 0 ≤ E₀ := (integral_nonneg (μ := ν) (fun t => sq_nonneg
    ‖markedNaturalPolynomial S c (t+σ+2*Real.pi*0)‖)).trans (hmean 0)
  have hE₁ : 0 ≤ E₁ := (integral_nonneg (μ := ν) (fun t => sq_nonneg
    ‖markedNaturalPolynomial S c (t+σ+2*Real.pi*0)‖)).trans
    (hcore 0 ⟨by linarith, hR.le⟩)
  have hi₁ : IntegrableOn (fun t => 2*‖∫ ξ in I, F ξ*A ξ t‖^2) W := hi.const_mul 2
  have hi₂ : IntegrableOn (fun t => 2*‖∫ ξ in Iᶜ, F ξ*A ξ t‖^2) W := hj.const_mul 2
  have hiSum : IntegrableOn (fun t =>
      2*‖∫ ξ in I, F ξ*A ξ t‖^2+2*‖∫ ξ in Iᶜ, F ξ*A ξ t‖^2) W := by
    change Integrable ((fun t => 2*‖∫ ξ in I, F ξ*A ξ t‖^2) +
      (fun t => 2*‖∫ ξ in Iᶜ, F ξ*A ξ t‖^2)) ν
    exact hi₁.add hi₂
  calc
    _ ≤ ∫ t in W, 2*‖∫ ξ in I, F ξ*A ξ t‖^2+2*‖∫ ξ in Iᶜ, F ξ*A ξ t‖^2 := by
      apply setIntegral_mono_on
      · exact (((markedNaturalPolynomial_continuous S (fun n => c n*ψ ((n:ℝ)/Y))).comp
          (continuous_id.add continuous_const)).norm.pow 2).integrableOn_Icc.mono_set inter_subset_left
      · exact hiSum
      · exact sourceComparisonHighTimes_measurable T B
      · intro t _
        rw [hcut, ← integral_add_compl hI (hInt t)]
        exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans
          (by nlinarith [sq_nonneg (‖∫ ξ in I, F ξ*A ξ t‖-‖∫ ξ in Iᶜ, F ξ*A ξ t‖)])
    _ = 2*(∫ t in W, ‖∫ ξ in I, F ξ*A ξ t‖^2)+2*(∫ t in W, ‖∫ ξ in Iᶜ, F ξ*A ξ t‖^2) := by
      rw [integral_add hi₁ hi₂, integral_const_mul, integral_const_mul]
    _ ≤ _ := by
      have hmain := hcoreBound.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (integral_nonneg (fun _ => norm_nonneg _)) hmass 2) hE₁)
      have htail := htailBound.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (integral_nonneg (fun _ => norm_nonneg _)) htailMass 2) hE₀)
      calc
        _ ≤ 2*((∫ ξ : ℝ, ‖F₀ ξ‖)^2*E₁)+
            2*(((∫ ξ : ℝ, |ξ|^j*‖F₀ ξ‖)/R^j)^2*E₀) :=
          add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num))
            (mul_le_mul_of_nonneg_left htail (by norm_num))
        _ = _ := by ring

end
end ArtinMatthews
