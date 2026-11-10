module

public import ArtinMatthews.QuadraticHeckeDualMellin
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaZero
public import ArtinMatthews.PrincipalDedekindProbeGrowth
public import ArtinMatthews.SourceQuadraticPoissonErrorMellin
public import ArtinMatthews.VaryingKummerAnalyticSmoothMellin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The two actual principal error kernels are continuous and absolutely
integrable on every positive contour that avoids the pole at one. -/
namespace ArtinMatthews
open NumberField Complex MeasureTheory Set VaryingKummerAnalytic SourcePhysical
open scoped ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]

def quadraticHeckeHalfZetaKernel (H : ℂ → ℂ) (σ t : ℝ) : ℂ :=
  (1 / 2 : ℂ) * H (((σ : ℂ) + (t : ℂ) * I) / 2) *
    mixedDedekindZeta F ((σ : ℂ) + (t : ℂ) * I)

def quadraticHeckeDualSquareErrorKernel (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (σ t : ℝ) : ℂ :=
  quadraticHeckeHalfZetaKernel F (quadraticHeckeDualMellin A r w) σ t

def quadraticHeckeOriginalSquareErrorKernel (w : ℝ → ℂ) (σ t : ℝ) : ℂ :=
  quadraticHeckeHalfZetaKernel F (mellin w) σ t

private theorem halfZetaKernel_continuous (H : ℂ → ℂ) (σ : ℝ) (hσ : σ ≠ 1)
    (hH : Continuous (fun t : ℝ => H (((σ : ℂ) + (t : ℂ) * I) / 2))) :
    Continuous (quadraticHeckeHalfZetaKernel F H σ) := by
  have hz : Continuous (fun t : ℝ => mixedDedekindZeta F ((σ : ℂ) + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (mixedDedekindZeta_analyticAt F ?_).continuousAt.comp' (f := _) (x := t) (by fun_prop)
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul,
      sub_zero, add_zero, one_re] at hre
    exact hσ hre
  exact (hH.const_mul (1 / 2 : ℂ)).mul hz

private theorem halfZetaKernel_height_bound (H : ℂ → ℂ) {σ : ℝ}
    (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1)
    (hH : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = σ / 2 →
      (1 + |s.im|) ^ k * ‖H s‖ ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖quadraticHeckeHalfZetaKernel F H σ t‖ ≤ C * sourceContourHeightWeight t := by
  obtain ⟨Cz, m, hCz, hz⟩ := exists_mixedDedekindZeta_vertical_polynomial_bound F
    σ (by linarith) hσtop hσone
  obtain ⟨Ch, hCh, hh⟩ := hH (m + 2)
  let D := 2 ^ (m + 2) * Ch
  refine ⟨Cz * (2 ^ m * D), by dsimp [D]; positivity, ?_⟩
  intro t
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hhalf_re : (s / 2).re = σ / 2 := by simp [s, div_ofNat_re]
  have hhalf_im : (s / 2).im = t / 2 := by simp [s, div_ofNat_im]
  have hH' := hh (s / 2) hhalf_re
  rw [hhalf_im] at hH'
  have ht : 1 + |t| ≤ 2 * (1 + |t / 2|) := by
    rw [abs_div]
    norm_num
    linarith [abs_nonneg t]
  have hrapid : (1 + |t|) ^ (m + 2) * ‖H (s / 2)‖ ≤ D := by
    calc
      _ ≤ (2 * (1 + |t / 2|)) ^ (m + 2) * ‖H (s / 2)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht _) (norm_nonneg _)
      _ = 2 ^ (m + 2) * ((1 + |t / 2|) ^ (m + 2) * ‖H (s / 2)‖) := by rw [mul_pow]; ring
      _ ≤ D := mul_le_mul_of_nonneg_left hH' (by positivity)
  have hw := sourceContourHeightWeight_of_rapid m t D _ (norm_nonneg _) hrapid
  have hhalf : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  change ‖(1 / 2 : ℂ) * H (s / 2) * mixedDedekindZeta F s‖ ≤ _
  calc
    _ ≤ ‖H (s / 2)‖ * (Cz * (|t| + 2) ^ m) := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_of_le_one_left (norm_nonneg _) hhalf)
        (hz t) (norm_nonneg _) (norm_nonneg _)
    _ = Cz * ((|t| + 2) ^ m * ‖H (s / 2)‖) := by ring
    _ ≤ Cz * ((2 ^ m * D) * sourceContourHeightWeight t) :=
      mul_le_mul_of_nonneg_left hw hCz.le
    _ = _ := by ring

private theorem halfZetaKernel_integrable (H : ℂ → ℂ) {σ : ℝ}
    (hσ : 0 < σ) (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1)
    (hHc : Continuous (fun t : ℝ => H (((σ : ℂ) + (t : ℂ) * I) / 2)))
    (hH : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = σ / 2 →
      (1 + |s.im|) ^ k * ‖H s‖ ≤ C) :
    Integrable (quadraticHeckeHalfZetaKernel F H σ) := by
  obtain ⟨C, _, hC⟩ := halfZetaKernel_height_bound F H hσ hσtop hσone hH
  exact (sourceContourHeightWeight_integrable.const_mul C).mono'
    (halfZetaKernel_continuous F H σ hσone hHc).aestronglyMeasurable (ae_of_all _ hC)

theorem quadraticHeckeDualSquareErrorKernel_continuous (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≠ 1) :
    Continuous (quadraticHeckeDualSquareErrorKernel F A r w σ) := by
  apply halfZetaKernel_continuous F _ σ hσone
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (quadraticHeckeDualMellin_differentiableAt A r w hcompact hpositive hsmooth.continuous
    _ (by simp only [div_ofNat_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]; positivity)).continuousAt.comp'
        (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I) / 2) (x := t) (by fun_prop)

theorem quadraticHeckeDualSquareErrorKernel_integrable (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ : ℝ} (hσ : 0 < σ)
    (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1) :
    Integrable (quadraticHeckeDualSquareErrorKernel F A r w σ) := by
  apply halfZetaKernel_integrable F _ hσ hσtop hσone
  · apply continuous_iff_continuousAt.mpr
    intro t
    exact (quadraticHeckeDualMellin_differentiableAt A r w hcompact hpositive hsmooth.continuous
      _ (by simp only [div_ofNat_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero]; positivity)).continuousAt.comp'
          (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I) / 2) (x := t) (by fun_prop)
  · intro k
    obtain ⟨C, hC, hb⟩ := quadraticHeckeDualMellin_strip_decay_pos A r w hcompact hpositive hsmooth
      (σ / 2) (σ / 2) (by positivity) k
    exact ⟨C, hC, fun s hs => hb s hs.ge hs.le⟩

theorem quadraticHeckeOriginalSquareErrorKernel_continuous (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ : ℝ} (hσone : σ ≠ 1) :
    Continuous (quadraticHeckeOriginalSquareErrorKernel F w σ) := by
  apply halfZetaKernel_continuous F _ σ hσone
  exact (smoothMellin_entire w hcompact hpositive hsmooth.continuous).continuous.comp (by fun_prop)

theorem quadraticHeckeOriginalSquareErrorKernel_integrable (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ : ℝ} (hσ : 0 < σ)
    (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1) :
    Integrable (quadraticHeckeOriginalSquareErrorKernel F w σ) := by
  apply halfZetaKernel_integrable F _ hσ hσtop hσone
  · exact (smoothMellin_entire w hcompact hpositive hsmooth.continuous).continuous.comp (by fun_prop)
  · intro k
    obtain ⟨C, hC, hb⟩ := smoothMellin_strip_decay w hcompact hpositive hsmooth (σ / 2) (σ / 2) k
    exact ⟨C, hC, fun s hs => hb s hs.ge hs.le⟩

end
end ArtinMatthews
