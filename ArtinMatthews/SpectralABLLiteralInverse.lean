module

public import ArtinMatthews.SpectralABLGaussianBound
public import ArtinMatthews.SpectralABLExceptionalBound
public import ArtinMatthews.SpectralKLWindowProperties
public import ArtinMatthews.SpectralABLWindowStripGrowth
public import ArtinMatthews.SpectralABLWindowSmooth


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
open scoped ContDiff
open scoped ComplexConjugate
noncomputable section

def spectralABLRegularInverse (T ε : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  spectralKLWindowSynthesis (spectralABLRegularWindow T (T ^ (1 - ε))) g

def spectralABLExceptionalInverse (a : ℝ) (A : ℕ) (g : ℝ → ℂ) : ℝ → ℂ :=
  spectralKLWindowSynthesis (spectralABLExceptionalWindow a A) g

theorem spectralABLRegularInverse_properties (T ε : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContinuousOn (spectralABLRegularInverse T ε g) (Ioi (0 : ℝ)) ∧
      MemLp (spectralABLRegularInverse T ε g) 2 spectralKLPhysicalMeasure ∧
      (∃ C : ℝ, 0 ≤ C ∧
        (∀ x : ℝ, 0 < x → ‖spectralABLRegularInverse T ε g x‖ ≤ C * x ^ (3 / 4 : ℝ)) ∧
        (∀ x : ℝ, 1 ≤ x → ‖spectralABLRegularInverse T ε g x‖ ≤ C / x ^ 2)) ∧
      (∀ ν : ℂ, |ν.re| ≤ 1 / 2 →
        spectralKLCompactOrderTransform (spectralABLRegularInverse T ε g) ν =
          spectralABLRegularWindow T (T ^ (1 - ε)) (-I * ν) * spectralKLCompactOrderTransform g ν) := by
  let Δ := T ^ (1 - ε)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT _
  obtain ⟨H, hH, hb⟩ := spectralABLRegularWindow_strip_polynomial T Δ hT hΔ
  have hstrip (t y : ℝ) (hy0 : 0 ≤ y) (hyB : y ≤ 3 / 4) :
      ‖spectralABLRegularWindow T Δ ((t : ℂ) + (y : ℂ) * I)‖ ≤ H * (1 + t ^ 2) :=
    hb t y (by rwa [abs_of_nonneg hy0])
  have hhol (z : ℂ) (_hz : |z.im| ≤ 3 / 4) : DifferentiableAt ℂ (spectralABLRegularWindow T Δ) z :=
    spectralABLRegularWindow_differentiable T Δ z
  simpa only [spectralABLRegularInverse, Δ] using
    spectralKLWindowSynthesis_properties (spectralABLRegularWindow T Δ) g hg hc hp
      (spectralABLRegularWindow_even T Δ) (spectralABLRegularWindow_real_contDiff T Δ)
      hhol (spectralABLRegularBound T Δ) (spectralABLRegularWindow_norm_le hT hΔ) H hH hstrip

theorem spectralABLExceptionalInverse_properties (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContinuousOn (spectralABLExceptionalInverse a A g) (Ioi (0 : ℝ)) ∧
      MemLp (spectralABLExceptionalInverse a A g) 2 spectralKLPhysicalMeasure ∧
      (∃ C : ℝ, 0 ≤ C ∧
        (∀ x : ℝ, 0 < x → ‖spectralABLExceptionalInverse a A g x‖ ≤ C * x ^ (3 / 4 : ℝ)) ∧
        (∀ x : ℝ, 1 ≤ x → ‖spectralABLExceptionalInverse a A g x‖ ≤ C / x ^ 2)) ∧
      (∀ ν : ℂ, |ν.re| ≤ 1 / 2 →
        spectralKLCompactOrderTransform (spectralABLExceptionalInverse a A g) ν =
          spectralABLExceptionalWindow a A (-I * ν) * spectralKLCompactOrderTransform g ν) := by
  obtain ⟨H, hH, hb⟩ := spectralABLExceptionalWindow_strip_polynomial a A hA
  have hstrip (t y : ℝ) (hy0 : 0 ≤ y) (hyB : y ≤ 3 / 4) :
      ‖spectralABLExceptionalWindow a A ((t : ℂ) + (y : ℂ) * I)‖ ≤ H * (1 + t ^ 2) :=
    hb t y (by rwa [abs_of_nonneg hy0])
  have hhol (z : ℂ) (hz : |z.im| ≤ 3 / 4) : DifferentiableAt ℂ (spectralABLExceptionalWindow a A) z := by
    have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
    exact spectralABLExceptionalWindow_differentiableAt a A z (by linarith)
  simpa only [spectralABLExceptionalInverse] using
    spectralKLWindowSynthesis_properties (spectralABLExceptionalWindow a A) g hg hc hp
      (spectralABLExceptionalWindow_even a A) (spectralABLExceptionalWindow_real_contDiff a hA)
      hhol (spectralABLExceptionalBound A) (spectralABLExceptionalWindow_norm_le a hA) H hH hstrip

theorem spectralABLRegularInverse_real (T ε : ℝ) (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (hg : ∀ x : ℝ, star (g x) = g x) (x : ℝ) :
    star (spectralABLRegularInverse T ε g x) = spectralABLRegularInverse T ε g x := by
  apply spectralKLWindowSynthesis_real _ g hp hg
  intro t
  change conj _ = _
  rw [spectralABLRegularWindow_real]
  exact conj_ofReal _

theorem spectralABLExceptionalInverse_real (a : ℝ) (A : ℕ) (g : ℝ → ℂ)
    (hp : tsupport g ⊆ Ioi (0 : ℝ)) (hg : ∀ x : ℝ, star (g x) = g x) (x : ℝ) :
    star (spectralABLExceptionalInverse a A g x) = spectralABLExceptionalInverse a A g x := by
  apply spectralKLWindowSynthesis_real _ g hp hg
  intro t
  change conj _ = _
  rw [spectralABLExceptionalWindow_real]
  exact conj_ofReal _

end
end ArtinMatthews
