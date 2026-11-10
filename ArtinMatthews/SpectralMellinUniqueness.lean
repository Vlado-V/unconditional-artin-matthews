module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.MellinInversion


set_option backward.privateInPublic true
@[expose] public section

/-! Mellin uniqueness derived from inversion of the difference.  No integrability
of either separate transformed function is assumed: the transform of the
integrable continuous difference is zero, hence is itself integrable. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectral_mellin_zero_of_vertical_zero (f : ℝ → ℂ) (σ : ℝ)
    (hf : MellinConvergent f σ)
    (hzero : ∀ t : ℝ, mellin f ((σ : ℂ)+t*Complex.I) = 0)
    {x : ℝ} (hx : 0 < x) (hc : ContinuousAt f x) : f x = 0 := by
  have hF : Complex.VerticalIntegrable (mellin f) σ := by
    unfold Complex.VerticalIntegrable
    simpa only [hzero] using! (integrable_zero ℝ ℂ volume)
  have h := mellinInv_mellin_eq σ f hx hf hF hc
  have hi : mellinInv σ (mellin f) x = 0 := by
    unfold mellinInv
    simp only [hzero,smul_zero,integral_zero]
  exact h.symm.trans hi

theorem spectral_mellin_unique (f g : ℝ → ℂ) (σ : ℝ)
    (hf : ∀ t : ℝ, MellinConvergent f ((σ : ℂ)+t*Complex.I))
    (hg : ∀ t : ℝ, MellinConvergent g ((σ : ℂ)+t*Complex.I))
    (heq : ∀ t : ℝ, mellin f ((σ : ℂ)+t*Complex.I) =
      mellin g ((σ : ℂ)+t*Complex.I))
    {x : ℝ} (hx : 0 < x) (hcf : ContinuousAt f x) (hcg : ContinuousAt g x) :
    f x = g x := by
  have hconv : MellinConvergent (fun y => f y-g y) σ := by
    simpa using (hasMellin_sub (hf 0) (hg 0)).1
  have hzero (t : ℝ) : mellin (fun y => f y-g y) ((σ : ℂ)+t*Complex.I) = 0 := by
    rw [(hasMellin_sub (hf t) (hg t)).2,heq t,sub_self]
  exact sub_eq_zero.mp (spectral_mellin_zero_of_vertical_zero (fun y => f y-g y) σ
    hconv hzero hx (hcf.sub hcg))

end ArtinMatthews
