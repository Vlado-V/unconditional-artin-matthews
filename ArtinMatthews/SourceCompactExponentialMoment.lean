module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Filter Metric
open scoped Topology
noncomputable section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A compact real log-weight gives an entire exponential moment. -/
theorem sourceCompactExponentialMoment_entire (μ : Measure X) (B : Set X)
    (hB : IsCompact B) (hBm : MeasurableSet B) (hμB : μ B ≠ ⊤)
    (L : X → ℝ) (hL : ContinuousOn L B) :
    Differentiable ℂ (fun s : ℂ => ∫ y in B, Complex.exp (s * (L y : ℂ)) ∂μ) := by
  intro s
  let ν := μ.restrict B
  letI : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hμB.lt_top⟩
  let F : ℂ → X → ℂ := fun z y => Complex.exp (z * (L y : ℂ))
  let G : ℂ → X → ℂ := fun z y => F z y * (L y : ℂ)
  have hFc (z : ℂ) : ContinuousOn (F z) B := by
    exact Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hL))
  have hGc : ContinuousOn (fun p : ℂ × X => G p.1 p.2) (closedBall s 1 ×ˢ B) := by
    have hl : ContinuousOn (fun p : ℂ × X => (L p.2 : ℂ)) (closedBall s 1 ×ˢ B) :=
      Complex.continuous_ofReal.comp_continuousOn
        (hL.comp continuous_snd.continuousOn (fun p hp => hp.2))
    exact (Complex.continuous_exp.comp_continuousOn
      (continuous_fst.continuousOn.mul hl)).mul hl
  obtain ⟨M,hM⟩ := ((isCompact_closedBall s 1).prod hB).exists_bound_of_continuousOn hGc
  have hFi : Integrable (F s) ν :=
    (hFc s).integrableOn_of_subset_isCompact hB hBm Subset.rfl hμB
  have hGi : AEStronglyMeasurable (G s) ν :=
    ((hFc s).mul (Complex.continuous_ofReal.comp_continuousOn hL)).aestronglyMeasurable hBm
  have hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) ν :=
    Eventually.of_forall (fun z => (hFc z).aestronglyMeasurable hBm)
  have hbound : ∀ᵐ y ∂ν, ∀ z ∈ ball s 1, ‖G z y‖ ≤ M := by
    filter_upwards [ae_restrict_mem hBm] with y hy z hz
    exact hM (z,y) ⟨ball_subset_closedBall hz,hy⟩
  have hd : ∀ᵐ y ∂ν, ∀ z ∈ ball s 1, HasDerivAt (fun w => F w y) (G z y) z := by
    filter_upwards with y z _
    simpa only [F,G,id_eq,one_mul] using ((hasDerivAt_id z).mul_const (L y : ℂ)).cexp
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := ν) (x₀ := s) (s := ball s 1) (F := F) (F' := G)
    (bound := fun _ => M) (ball_mem_nhds s zero_lt_one) hmeas hFi hGi hbound
    (integrable_const M) hd).2.differentiableAt

end
end ArtinMatthews
