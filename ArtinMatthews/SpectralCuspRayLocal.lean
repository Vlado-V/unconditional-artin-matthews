module

public import ArtinMatthews.SpectralCuspWeakRegularityPrimitives
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Complex.RealDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! Local integrability and actual primitives on an arbitrary cusp tail. -/
namespace ArtinMatthews.SpectralCuspRayRegularity
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
variable {Y : ℝ}

theorem ray_interval_integrable {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : LocallyIntegrableOn f (Ioi Y) volume)
    {a b : ℝ} (ha : Y < a) (hb : Y < b) : IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_iff').mpr
  apply hf.integrableOn_compact_subset _ isCompact_uIcc
  intro x hx
  exact lt_of_lt_of_le (lt_min ha hb) hx.1

theorem integrable_ray_test_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : LocallyIntegrableOn f (Ioi Y) volume)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) : Integrable (fun x => ρ x • f x) volume := by
  have hfi : Integrable ((tsupport ρ).indicator f) volume :=
    (integrable_indicator_iff (isClosed_tsupport ρ).measurableSet).mpr
      (hf.integrableOn_compact_subset hρs hρc)
  have H := hfi.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hρ hρc
  apply H.congr
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ tsupport ρ
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, smul_zero,
        image_eq_zero_of_notMem_tsupport hx, zero_smul]

theorem ray_test_setIntegral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {ρ : ℝ → ℝ} (hρs : tsupport ρ ⊆ Ioi Y) :
    (∫ x in Ioi Y, ρ x • f x) = ∫ x, ρ x • f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hρs h)), zero_smul]

theorem ray_primitive_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : LocallyIntegrableOn f (Ioi Y) volume) :
    ContinuousOn (fun x => ∫ t in (Y+1)..x, f t) (Ioi Y) := by
  intro x hx
  change Y < x at hx
  let a := (Y+min (Y+1) x)/2
  let b := max (Y+1) x+1
  have ha : Y < a := by dsimp [a]; have := lt_min (by linarith : Y<Y+1) hx; linarith
  have ha1 : a < Y+1 := by
    have := min_le_left (Y+1) x
    dsimp [a]
    linarith
  have hb1 : Y+1 < b := by
    have := le_max_left (Y+1) x
    dsimp [b]
    linarith
  have hax : a < x := by
    have := min_le_right (Y+1) x
    dsimp [a]
    linarith
  have hxb : x < b := by
    have := le_max_right (Y+1) x
    dsimp [b]
    linarith
  have hab : a ≤ b := by linarith
  have h1 : Y+1 ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨ha1.le,hb1.le⟩
  have H := intervalIntegral.continuousOn_primitive_interval'
    (ray_interval_integrable hf ha (by linarith : Y<b)) h1
  have hnb : uIcc a b ∈ 𝓝 x := by rw [uIcc_of_le hab]; exact Icc_mem_nhds hax hxb
  exact (H.continuousAt hnb).continuousWithinAt

end
end ArtinMatthews.SpectralCuspRayRegularity
