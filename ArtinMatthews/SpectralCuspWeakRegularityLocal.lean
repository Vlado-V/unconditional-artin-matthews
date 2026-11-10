module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Positivity.Finset
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Local integrability and actual primitive geometry on the positive
half-line. Compact tests are supported away from its singular endpoint. -/
namespace ArtinMatthews.SpectralCuspWeakRegularity
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

theorem positive_interval_integrable {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)) volume)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_iff').mpr
  apply hf.integrableOn_compact_subset _ isCompact_uIcc
  intro x hx
  exact lt_of_lt_of_le (lt_min ha hb) hx.1

theorem integrable_positive_test_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)) volume)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi (0 : ℝ)) : Integrable (fun x => ρ x • f x) volume := by
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

theorem positive_test_setIntegral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {ρ : ℝ → ℝ} (hρs : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    (∫ x in Ioi (0 : ℝ), ρ x • f x) = ∫ x, ρ x • f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hn : x ∉ tsupport ρ := fun h => hx (hρs h)
  rw [image_eq_zero_of_notMem_tsupport hn, zero_smul]

theorem positive_primitive_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : LocallyIntegrableOn f (Ioi (0 : ℝ)) volume) :
    ContinuousOn (fun x => ∫ t in (1 : ℝ)..x, f t) (Ioi (0 : ℝ)) := by
  intro x hx
  change (0 : ℝ) < x at hx
  let a := min 1 x / 2
  let b := max 1 x + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := by
    have h1 := min_le_left (1 : ℝ) x
    have h2 := le_max_left (1 : ℝ) x
    dsimp [a, b]
    linarith
  have ha1 : a < 1 := by
    have h := min_le_left (1 : ℝ) x
    dsimp [a]
    linarith
  have hb1 : 1 < b := by
    have h := le_max_left (1 : ℝ) x
    dsimp [b]
    linarith
  have hax : a < x := by
    have h := min_le_right (1 : ℝ) x
    dsimp [a]
    linarith
  have hxb : x < b := by
    have h := le_max_right (1 : ℝ) x
    dsimp [b]
    linarith
  have h1 : (1 : ℝ) ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨ha1.le, hb1.le⟩
  have H := intervalIntegral.continuousOn_primitive_interval'
    (positive_interval_integrable hf ha (by linarith : 0 < b)) h1
  have hnb : uIcc a b ∈ 𝓝 x := by
    rw [uIcc_of_le hab]
    exact Icc_mem_nhds hax hxb
  exact (H.continuousAt hnb).continuousWithinAt

end
end ArtinMatthews.SpectralCuspWeakRegularity
