module

public import ArtinMatthews.SpectralEisensteinBoundedLog
public import ArtinMatthews.SpectralEisensteinVerticalCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Clamping the log only outside a fixed compact height range gives a
genuine entire Banach-valued extension of the cutoff height monomial. -/
noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace ArtinMatthews

section
variable {X : Type*} [TopologicalSpace X]

def spectralBoundedHeightLog (H : X → ℝ) (hH : Continuous H) (hp : ∀ z, 0<H z) (M : ℝ)
    (hM : 1≤M) : X →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => (max 0 (min (Real.log M) (Real.log (H z))):ℝ))
    (Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.min
      (hH.log (fun z => (hp z).ne'))))) (Real.log M) (fun z => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
      exact max_le (Real.log_nonneg hM) (min_le_left _ _))

theorem spectralBoundedHeightLog_eq (H : X → ℝ) (hH : Continuous H) (hp : ∀ z, 0<H z)
    (M : ℝ) (hM : 1≤M) (z : X) (hz : H z∈Icc 1 M) :
    spectralBoundedHeightLog H hH hp M hM z=(Real.log (H z):ℂ) := by
  change ((max 0 (min (Real.log M) (Real.log (H z))):ℝ):ℂ)=(Real.log (H z):ℂ)
  rw [min_eq_right (Real.log_le_log (hp z) hz.2),max_eq_right (Real.log_nonneg hz.1)]

def spectralBoundedHeightCutoff (H : X → ℝ) (hH : Continuous H) : X →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => (eisensteinHeightCutoff (H z):ℂ))
    (Complex.continuous_ofReal.comp (eisensteinHeightCutoff_contDiff.continuous.comp hH)) 1
    (fun z => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (eisensteinHeightCutoff_range (H z)).1]
      exact (eisensteinHeightCutoff_range (H z)).2)

def spectralCompactCutoffExponential (H : X → ℝ) (hH : Continuous H) (hp : ∀ z, 0<H z) (M : ℝ)
    (hM : 1≤M) (s : ℂ) : X →ᵇ ℂ :=
  spectralBoundedHeightCutoff H hH * spectralBoundedExponential (spectralBoundedHeightLog H hH hp M hM) s

theorem spectralCompactCutoffExponential_analyticAt (H : X → ℝ) (hH : Continuous H)
    (hp : ∀ z, 0<H z) (M : ℝ) (hM : 1≤M) (s : ℂ) :
    AnalyticAt ℂ (spectralCompactCutoffExponential H hH hp M hM) s :=
  analyticAt_const.mul (spectralBoundedExponential_analyticAt _ s)

theorem spectralCompactCutoffExponential_eq (H : X → ℝ) (hH : Continuous H) (hp : ∀ z, 0<H z)
    (M : ℝ) (hM : 1≤M) (s : ℂ) (z : X) (hz : H z≤M) :
    spectralCompactCutoffExponential H hH hp M hM s z=eisensteinVerticalCutoffMode s (H z) := by
  change (eisensteinHeightCutoff (H z):ℂ)*
    spectralBoundedExponential (spectralBoundedHeightLog H hH hp M hM) s z=
    (eisensteinHeightCutoff (H z):ℂ)*(H z:ℂ)^s
  by_cases hlo : H z≤1
  · rw [eisensteinHeightCutoff_zero hlo,Complex.ofReal_zero,zero_mul,zero_mul]
  · rw [spectralBoundedExponential_apply,
      spectralBoundedHeightLog_eq H hH hp M hM z ⟨(lt_of_not_ge hlo).le,hz⟩,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hp z).ne'),
      ← Complex.ofReal_log (hp z).le,mul_comm s]

end
end ArtinMatthews
