module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.CubicMoment.Estimates.MellinSmooth
public import OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference


set_option backward.privateInPublic true
@[expose] public section

/-!
# Smooth Mellin transforms for the varying-field explicit formula

The transform is Mathlib's literal Mellin integral.  Compact support in the
positive half-line supplies convergence, entire continuation, arbitrary-order
decay on every fixed closed vertical strip, and inversion.  All constants
depend only on the fixed weight, strip, and decay order, independently of any
number field.

The analytic proofs are reused from the checked OAI smooth Mellin and compact
Fourier-family bounds; no transform estimates are hypotheses here.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace ArtinMatthews.VaryingKummerAnalytic

/-- A compact positive support lies in an actual interval bounded away from zero. -/
theorem smoothMellin_positive_support_interval
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ tsupport f ⊆ Icc a b := by
  by_cases hne : (tsupport f).Nonempty
  · obtain ⟨a, ha⟩ := hcompact.isCompact.exists_isLeast hne
    obtain ⟨b, hb⟩ := hcompact.isCompact.exists_isGreatest hne
    exact ⟨a, b, hpositive ha.1, fun _ ht => ⟨ha.2 ht, hb.2 ht⟩⟩
  · refine ⟨1, 1, by norm_num, ?_⟩
    rw [not_nonempty_iff_eq_empty.mp hne]
    exact empty_subset _

/-- Compatibility with the usual integral convention, with the weight written first. -/
theorem smoothMellin_eq_integral (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ t : ℝ in Ioi 0, f t * (t : ℂ) ^ (s - 1) := by
  simp only [mellin, smul_eq_mul, mul_comm]

/-- The actual defining integral converges at every complex argument. -/
theorem smoothMellin_convergent
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hcontinuous : Continuous f) (s : ℂ) :
    MellinConvergent f s :=
  OAI.CubicFirstMoment.smooth_mellin_convergent f hcompact hpositive hcontinuous s

/-- The literal Mellin transform of a continuous compact positive weight is entire. -/
theorem smoothMellin_entire
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hcontinuous : Continuous f) :
    Differentiable ℂ (mellin f) :=
  OAI.CubicFirstMoment.smooth_mellin_entire f hcompact hpositive hcontinuous

theorem smoothMellin_analyticAt
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hcontinuous : Continuous f) (s : ℂ) :
    AnalyticAt ℂ (mellin f) s :=
  (smoothMellin_entire f hcompact hpositive hcontinuous).analyticAt s

/-- Uniform rapid decay on any fixed finite vertical strip. -/
theorem smoothMellin_strip_decay
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f)
    (lo hi : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi →
      (1 + |s.im|) ^ A * ‖mellin f s‖ ≤ C := by
  obtain ⟨a, b, ha, hsupp⟩ := smoothMellin_positive_support_interval f hcompact hpositive
  obtain ⟨C, hC, hbound⟩ := OAI.CubicReflectionKernel.compact_source_mellin_strip_decay
    f a b ha ((subset_tsupport f).trans hsupp) hsmooth lo hi A
  refine ⟨C, hC, fun s hlo hhi => ?_⟩
  simpa only [Complex.re_add_im] using hbound s.re ⟨hlo, hhi⟩ s.im

/-- The exact strip used in the varying-field explicit formula. -/
theorem smoothMellin_explicitFormula_decay
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖mellin f s‖ ≤ C / (1 + |s.im|) ^ A := by
  obtain ⟨C, hC, hbound⟩ :=
    smoothMellin_strip_decay f hcompact hpositive hsmooth (-(1 / 2)) 2 A
  refine ⟨C, hC, fun s hlo hhi => ?_⟩
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + |s.im|) A)).mpr
  simpa only [mul_comm] using hbound s hlo hhi

/-- Smooth support supplies absolute vertical integrability on every line. -/
theorem smoothMellin_verticalIntegrable
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin f) σ :=
  OAI.CubicFirstMoment.smooth_mellin_vertical_integrable f hcompact hpositive hsmooth σ

/-- Mellin inversion with convergence discharged from the actual smooth support. -/
theorem smoothMellin_inversion
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f)
    (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin f) x = f x :=
  OAI.CubicFirstMoment.smooth_mellin_inversion f hcompact hpositive hsmooth σ hx

theorem smoothMellin_inversion_two
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f)
    {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (mellin f) x = f x :=
  smoothMellin_inversion f hcompact hpositive hsmooth 2 hx

/-- The inversion formula with its literal absolutely convergent vertical integral. -/
theorem smoothMellin_inversion_integral
    (f : ℝ → ℂ) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (hsmooth : ContDiff ℝ ∞ f)
    (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) *
        mellin f ((σ : ℂ) + y * Complex.I)) = f x := by
  simpa only [mellinInv, smul_eq_mul, Complex.real_smul] using
    smoothMellin_inversion f hcompact hpositive hsmooth σ hx

end ArtinMatthews.VaryingKummerAnalytic
