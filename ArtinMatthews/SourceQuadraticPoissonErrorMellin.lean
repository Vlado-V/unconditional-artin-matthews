module

public import ArtinMatthews.QuadraticHeckeDualMellin
public import ArtinMatthews.SourceContourHeightWeight
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaZero
public import ArtinMatthews.PrincipalDedekindProbeGrowth
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

/-! The positive lines used for the dual square-profile errors. The
recurrence for the gamma ratio allows the contour to approach zero
while keeping its real part strictly positive. -/

namespace ArtinMatthews
open Complex MeasureTheory Set VaryingKummerAnalytic
open scoped ContDiff

noncomputable section

private theorem quadraticHeckeDualGamma_add_one (A : ℝ) (r : ℕ) (s : ℂ)
    (hs : s ≠ 0) :
    quadraticHeckeDualGamma A r (s + 1) =
      Complex.exp (2 * (Real.log A : ℂ)) * (-s * s) ^ r * quadraticHeckeDualGamma A r s := by
  have hstep : Gamma (s + 1) / Gamma (1 - (s + 1)) =
      (-s * s) * (Gamma s / Gamma (1 - s)) := by
    rw [show 1 - (s + 1) = -s by ring, show 1 - s = -s + 1 by ring,
      Gamma_add_one s hs, Gamma_add_one (-s) (neg_ne_zero.mpr hs)]
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      _ = s * Gamma s * (Gamma (-s))⁻¹ := rfl
      _ = ((-s) * (-s)⁻¹) * (s * Gamma s * (Gamma (-s))⁻¹) := by
        rw [mul_inv_cancel₀ (neg_ne_zero.mpr hs), one_mul]
      _ = _ := by ring
  unfold quadraticHeckeDualGamma
  rw [hstep, mul_pow]
  have he : (2 * (s + 1) - 1) * (Real.log A : ℂ) =
      2 * (Real.log A : ℂ) + (2 * s - 1) * (Real.log A : ℂ) := by ring
  rw [he, Complex.exp_add]
  ring

private theorem exists_quadraticHeckeDualGamma_strip_bound_pos (A : ℝ) (r : ℕ)
    (u v : ℝ) (hu : 0 < u) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      ‖quadraticHeckeDualGamma A r s‖ ≤ C * (1 + |s.im|) ^ n := by
  obtain ⟨B, hB⟩ := exists_nat_gt (v + 1)
  obtain ⟨C, hC, hb⟩ := exists_quadraticHeckeDualGamma_strip_bound A r B
  let K := Real.exp (2 * Real.log A) * (u * u) ^ r
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨(2 * B + 2) * r, C / K, div_pos hC hK, ?_⟩
  intro s hs₀ hs₁
  have hs : s ≠ 0 := by
    intro h
    simp [h, not_le.mpr hu] at hs₀
  have hsu : u ≤ ‖s‖ := hs₀.trans (re_le_norm _)
  have hpow := pow_le_pow_left₀ (mul_nonneg hu.le hu.le)
    (mul_le_mul hsu hsu hu.le (norm_nonneg s)) r
  have h := hb (s + 1) (by simp only [add_re, one_re]; linarith)
    (by simp only [add_re, one_re]; linarith)
  rw [quadraticHeckeDualGamma_add_one A r s hs, norm_mul, norm_mul, norm_pow,
    norm_mul, norm_neg, norm_exp] at h
  have hreal : ((2 : ℂ) * (Real.log A : ℂ)).re = 2 * Real.log A := by
    norm_num [Complex.mul_re]
  rw [hreal, add_im, one_im, add_zero] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hK).mpr
  calc
    _ = K * ‖quadraticHeckeDualGamma A r s‖ := mul_comm _ _
    _ ≤ Real.exp (2 * Real.log A) * (‖s‖ * ‖s‖) ^ r *
        ‖quadraticHeckeDualGamma A r s‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)) (norm_nonneg _)
    _ ≤ _ := h

/-- Arbitrary rapid decay on every compact real strip strictly to the right of zero. -/
theorem quadraticHeckeDualMellin_strip_decay_pos (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) (u v : ℝ) (hu : 0 < u) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      (1 + |s.im|) ^ k * ‖quadraticHeckeDualMellin A r w s‖ ≤ C := by
  obtain ⟨n, Cγ, hCγ, hγ⟩ := exists_quadraticHeckeDualGamma_strip_bound_pos A r u v hu
  obtain ⟨Cw, hCw, hw⟩ := smoothMellin_strip_decay w hcompact hpositive hsmooth
    (1 - v) (1 - u) (k + n)
  refine ⟨Cγ * Cw, mul_pos hCγ hCw, ?_⟩
  intro s hlo hhi
  have hm := hw (1 - s) (by simp only [sub_re, one_re]; linarith)
    (by simp only [sub_re, one_re]; linarith)
  simp only [sub_im, one_im, zero_sub, abs_neg] at hm
  let T : ℝ := 1 + |s.im|
  have hT : 0 < T := by dsimp [T]; positivity
  rw [quadraticHeckeDualMellin, norm_mul]
  calc
    _ ≤ T ^ k * ((Cγ * T ^ n) * ‖mellin w (1 - s)‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hγ s hlo hhi) (norm_nonneg _)) (pow_nonneg hT.le _)
    _ = Cγ * (T ^ (k + n) * ‖mellin w (1 - s)‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm hCγ.le


theorem quadraticHeckeDualMellin_verticalIntegrable_pos (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t : ℝ => quadraticHeckeDualMellin A r w ((σ : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨C, _, hdecay⟩ := quadraticHeckeDualMellin_strip_decay_pos A r w
    hcompact hpositive hsmooth σ σ hσ 2
  have hcont : Continuous (fun t : ℝ =>
      quadraticHeckeDualMellin A r w ((σ : ℂ) + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (quadraticHeckeDualMellin_differentiableAt A r w hcompact hpositive
      hsmooth.continuous _ (by simpa using hσ)).continuousAt.comp'
        (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) (x := t) (by fun_prop)
  refine (SourcePhysical.sourceContourHeightWeight_integrable.const_mul C).mono'
    hcont.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  have h := hdecay ((σ : ℂ) + (t : ℂ) * I) (by simp) (by simp)
  have h' := SourcePhysical.sourceContourHeightWeight_of_rapid 0 t C _
    (norm_nonneg _) (by simpa using h)
  simpa only [pow_zero, one_mul] using h'

/-- The square-profile symbol on the actual principal zeta line is integrable
on every positive line away from the pole at one. -/
theorem quadraticHeckeDualSquareZeta_height_bound (F : Type) [Field F] [NumberField F]
    (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {σ : ℝ} (hσ : 0 < σ)
    (hσtop : σ ≤ 5 / 4) (hσone : σ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖(1 / 2 : ℂ) * quadraticHeckeDualMellin A r w
        (((σ : ℂ) + (t : ℂ) * I) / 2) *
          mixedDedekindZeta F ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * SourcePhysical.sourceContourHeightWeight t := by
  obtain ⟨Cz, m, hCz, hz⟩ := exists_mixedDedekindZeta_vertical_polynomial_bound F
    σ (by linarith) hσtop hσone
  obtain ⟨Ch, hCh, hh⟩ := quadraticHeckeDualMellin_strip_decay_pos A r w hcompact
    hpositive hsmooth (σ / 2) (σ / 2) (by positivity) (m + 2)
  let D := 2 ^ (m + 2) * Ch
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨Cz * (2 ^ m * D), by positivity, ?_⟩
  intro t
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hhalf_re : (s / 2).re = σ / 2 := by simp [s, div_ofNat_re]
  have hhalf_im : (s / 2).im = t / 2 := by simp [s, div_ofNat_im]
  have hH := hh (s / 2) (by rw [hhalf_re]) (by rw [hhalf_re])
  rw [hhalf_im] at hH
  have ht : 1 + |t| ≤ 2 * (1 + |t / 2|) := by
    rw [abs_div]
    norm_num
    linarith [abs_nonneg t]
  have hrapid : (1 + |t|) ^ (m + 2) * ‖quadraticHeckeDualMellin A r w (s / 2)‖ ≤ D := by
    calc
      _ ≤ (2 * (1 + |t / 2|)) ^ (m + 2) *
          ‖quadraticHeckeDualMellin A r w (s / 2)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht _) (norm_nonneg _)
      _ = 2 ^ (m + 2) * ((1 + |t / 2|) ^ (m + 2) *
          ‖quadraticHeckeDualMellin A r w (s / 2)‖) := by rw [mul_pow]; ring
      _ ≤ D := mul_le_mul_of_nonneg_left hH (by positivity)
  have hw := SourcePhysical.sourceContourHeightWeight_of_rapid m t D _
    (norm_nonneg _) hrapid
  have hhalf : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  calc
    _ ≤ ‖quadraticHeckeDualMellin A r w (s / 2)‖ *
        (Cz * (|t| + 2) ^ m) := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_of_le_one_left (norm_nonneg _) hhalf)
        (hz t) (norm_nonneg _) (norm_nonneg _)
    _ = Cz * ((|t| + 2) ^ m * ‖quadraticHeckeDualMellin A r w (s / 2)‖) := by ring
    _ ≤ Cz * ((2 ^ m * D) * SourcePhysical.sourceContourHeightWeight t) :=
      mul_le_mul_of_nonneg_left hw hCz.le
    _ = _ := by ring

end
end ArtinMatthews
