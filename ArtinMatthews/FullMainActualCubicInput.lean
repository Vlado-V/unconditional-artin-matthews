module

public import ArtinMatthews.CubicPrimeTraceActual
public import ArtinMatthews.FullMainConditionalInputs


set_option backward.privateInPublic true
@[expose] public section

/-! The actual cubic-selected mean is supplied by the same ordinary
tuple cancellation used by the final endpoint. -/

noncomputable section
namespace ArtinMatthews

open scoped ContDiff

theorem GiantOrdinaryTupleCancellationInput.cubic_selected_mean
    {ε : ℝ} {Φ : ℝ → ℝ} (htuple : GiantOrdinaryTupleCancellationInput ε Φ)
    (hε : 0 < ε) (hεq : ε < 1/4)
    (hΦsmooth : ContDiff ℝ ∞ Φ) (hΦcompact : HasCompactSupport Φ)
    (hΦrange : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1) :
    GiantCubicSelectedMeanInput ε Φ := by
  intro S hS _ _ T hT₁ hT₂ hs M instM h₃ U hU₃
  exact giantCubicFrobenius_mean_of_ordinary_mean hS h₃ U hU₃ hε hεq hT₁ hT₂
    Φ hΦsmooth hΦrange hs (by
      simpa only [mul_assoc] using
        htuple.finite_mean hε hεq hΦsmooth hΦcompact (fun t => (hΦrange t).1) hT₁ hT₂ hs M U)

theorem fullMainStatement_of_actual_tuple_angular_inputs
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε < 1/1000000)
    (Φ : ℝ → ℝ) (hΦsmooth : ContDiff ℝ ∞ Φ)
    (hΦcompact : HasCompactSupport Φ) (hΦsupport : tsupport Φ ⊆ Set.Ioo (1 : ℝ) 2)
    (hΦrange : ∀ t, 0 ≤ Φ t ∧ Φ t ≤ 1) (hΦnonzero : ∃ t, Φ t ≠ 0)
    (htuple : GiantOrdinaryTupleCancellationInput ε Φ)
    (hsource : GiantAngularSourceInput) : FullMainStatement :=
  fullMainStatement_of_actual_tuple_cubic_angular_inputs hε hεδ Φ hΦsmooth hΦcompact
    hΦsupport hΦrange hΦnonzero htuple
    (htuple.cubic_selected_mean hε (hεδ.trans (by norm_num)) hΦsmooth hΦcompact hΦrange)
    hsource

end ArtinMatthews
