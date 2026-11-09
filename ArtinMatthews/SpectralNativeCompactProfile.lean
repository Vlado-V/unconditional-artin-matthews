module

public import ArtinMatthews.SpectralKLHeightPhysicalTest
public import Mathlib.Analysis.SpecialFunctions.Sqrt


set_option backward.privateInPublic true
@[expose] public section

/-! The physical profile of an actual compact smooth height test is a
compact smooth real-valued input for the inverse-KL construction. -/

noncomputable section
open Set Filter
open scoped ContDiff
namespace ArtinMatthews

theorem spectralKLHeightPhysicalTest_contDiff {q : ℝ} (hq : 0 < q)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) : ContDiff ℝ ∞ (spectralKLHeightPhysicalTest q ρ) := by
  have hsupport := (spectralKLHeightPhysicalTest_properties hq ρ hρ.continuous hcρ hpρ).2.2
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · have hy : 0 < x/q := div_pos hx hq
    have harg : ContDiffAt ℝ ∞ (fun y : ℝ => y/q) x := by fun_prop
    have hr : ContDiffAt ℝ ∞ (fun y : ℝ => ρ (y/q)*Real.sqrt (y/q)/(y/q)) x :=
      ((hρ.contDiffAt.comp x harg).mul (harg.sqrt hy.ne')).div harg hy.ne'
    have hc : ContDiffAt ℝ ∞ (fun y : ℝ => ((ρ (y/q)*Real.sqrt (y/q)/(y/q) : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hr
    change ContDiffAt ℝ ∞ (fun y : ℝ =>
      ((ρ (y/q)*Real.sqrt (y/q) : ℝ) : ℂ)/((y/q : ℝ) : ℂ)) x
    convert hc using 1
    funext y
    simp only [Complex.ofReal_div]
  · have hn : x ∉ tsupport (spectralKLHeightPhysicalTest q ρ) := fun h => hx (hsupport h)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem spectralKLHeightPhysicalTest_conj (q : ℝ) (ρ : ℝ → ℝ) (x : ℝ) :
    star (spectralKLHeightPhysicalTest q ρ x) = spectralKLHeightPhysicalTest q ρ x := by
  simp [spectralKLHeightPhysicalTest,spectralKLHeightBaseTest]

end ArtinMatthews
