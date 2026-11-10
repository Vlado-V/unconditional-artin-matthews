module

public import ArtinMatthews.QuadraticHeckePrincipalNormContour
public import ArtinMatthews.QuadraticHeckeFieldNormalization
public import ArtinMatthews.QuadraticHeckeDualProfile
public import ArtinMatthews.PrincipalDedekindProbeBoundary
public import ArtinMatthews.QuadraticHeckeDualInversion
public import ArtinMatthews.QuadraticHeckeNormSmoothing
public import ArtinMatthews.QuadraticHeckePrincipalNormSeries
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! Mellin–Poisson summation of a compact positive weight over genuine nonzero
integral ideals in the totally complex principal row. -/

namespace ArtinMatthews
open NumberField Complex Set MeasureTheory VaryingKummerAnalytic
open OAI.SevenEighths.ProbePhysical
open scoped NumberField ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "r" => InfinitePlace.nrComplexPlaces F
local notation "A" => quadraticHeckeFieldScale F
local notation "Ideals" => {I : Ideal (𝓞 F) // I ≠ ⊥}

variable (w : ℝ → ℂ)

theorem quadraticHeckePrincipalNormContour_right
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    (∑' I : Ideals, w ((Ideal.absNorm I.val : ℝ) / X)) =
      verticalIntegral (5 / 4) (quadraticHeckePrincipalIntegrand F w X) := by
  let : Countable Ideals := quadraticHeckePrincipalIdeal_countable F
  have h := quadraticHeckeNormSmoothing_contour
    (fun I : Ideals => (Ideal.absNorm I.val : ℝ)) (quadraticHeckePrincipalIdealNorm_pos F)
    (fun _ => 1) (mellin w) (5 / 4)
    ((smoothMellin_entire w hcompact hpositive hsmooth.continuous).continuous.comp (by fun_prop))
    (smoothMellin_verticalIntegrable w hcompact hpositive hsmooth (5 / 4))
    (by simpa only [norm_one, one_mul] using
      quadraticHeckePrincipalIdealNorm_summable F (σ := 5 / 4) (by norm_num)) hX
  simp only [one_mul] at h
  have hInv (J : Ideals) :
      mellinInv (5 / 4) (mellin w) ((Ideal.absNorm J.val : ℝ) / X) =
        w ((Ideal.absNorm J.val : ℝ) / X) :=
    smoothMellin_inversion w hcompact hpositive hsmooth _
      (div_pos (quadraticHeckePrincipalIdealNorm_pos F J) hX)
  simp_rw [hInv] at h
  rw [h, verticalIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  let s : ℂ := ((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I
  have hs : 1 < s.re := by norm_num [s]
  change (X : ℂ) ^ s * mellin w s * (∑' I : Ideals, ((Ideal.absNorm I.val : ℝ) : ℂ) ^ (-s)) =
    quadraticHeckePrincipalIntegrand F w X s
  rw [quadraticHeckePrincipalIntegrand, mixedDedekindZeta_eq F hs,
    quadraticHeckePrincipalIdealSeries_eq_zeta F hs]

theorem quadraticHeckePrincipalNormPoisson_dual_summable
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    Summable (fun I : Ideals =>
      ‖quadraticHeckeDualProfile A r w (X * (Ideal.absNorm I.val : ℝ))‖) := by
  obtain ⟨C, _, hC⟩ := quadraticHeckeDualProfile_power_bound A r w hcompact hpositive hsmooth
    (σ := 5 / 4) (by norm_num)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun I => ?_)
    ((quadraticHeckePrincipalIdealNorm_summable F (σ := 5 / 4) (by norm_num)).mul_left
      (C * X ^ (- (5 / 4 : ℝ))))
  have hq := quadraticHeckePrincipalIdealNorm_pos F I
  have h := hC _ (mul_pos hX hq)
  rw [Real.mul_rpow hX.le hq.le, ← mul_assoc] at h
  exact h

variable [IsTotallyComplex F]

theorem quadraticHeckePrincipalZeta_reflection {s : ℂ} (hs : s.re < 0) :
    mixedDedekindZeta F s =
      quadraticHeckeDualGamma A r (1 - s) * dedekindZeta F (1 - s) := by
  have hne : s ≠ 1 := by
    intro h
    norm_num [h] at hs
  have h := principalDedekindRegularized_left_reflection F hs
  rw [principalDedekindRegularized_eq_zeta F hne] at h
  have he : 2 * (1 - s) - 1 = 1 - 2 * s := by ring
  have hr : 1 - (1 - s) = s := by ring
  rw [quadraticHeckeDualGamma_eq_mixed F, he, hr]
  apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
  exact h.trans (by ring)

private theorem principalContour_reflect {X : ℝ} (hX : 0 < X) (s : ℂ) (hs : 1 < s.re) :
    quadraticHeckePrincipalIntegrand F w X (1 - s) =
      (X : ℂ) * (((X⁻¹ : ℝ) : ℂ) ^ s * quadraticHeckeDualMellin A r w s * dedekindZeta F s) := by
  have hpow : (X : ℂ) ^ (1 - s) = (X : ℂ) * (((X⁻¹ : ℝ) : ℂ) ^ s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'),
      Complex.cpow_one, Complex.cpow_neg, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hX.le]
  have hneg : (1 - s).re < 0 := by simp only [sub_re, one_re]; linarith
  have hr : 1 - (1 - s) = s := by ring
  rw [quadraticHeckePrincipalIntegrand, quadraticHeckePrincipalZeta_reflection F hneg,
    hr, hpow, quadraticHeckeDualMellin]
  ring

omit [IsTotallyComplex F] in
theorem quadraticHeckePrincipalDualSeries_eq_integral
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    (∑' I : Ideals, quadraticHeckeDualProfile A r w (X * (Ideal.absNorm I.val : ℝ))) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, ((X⁻¹ : ℝ) : ℂ) ^ (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I) *
          quadraticHeckeDualMellin A r w (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I) *
            dedekindZeta F (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I) := by
  let : Countable Ideals := quadraticHeckePrincipalIdeal_countable F
  let L (t : ℝ) : ℂ := ((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I
  have hL : Continuous L := by unfold L; fun_prop
  have hM : Continuous (fun t => quadraticHeckeDualMellin A r w (L t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (quadraticHeckeDualMellin_differentiableAt A r w hcompact hpositive hsmooth.continuous
      (L t) (by norm_num [L])).continuousAt.comp' (f := L) (x := t) hL.continuousAt
  have h := quadraticHeckeNormSmoothing_contour
    (fun I : Ideals => (Ideal.absNorm I.val : ℝ)) (quadraticHeckePrincipalIdealNorm_pos F)
    (fun _ => 1) (quadraticHeckeDualMellin A r w) (5 / 4) hM
    (quadraticHeckeDualMellin_verticalIntegrable A r w hcompact hpositive hsmooth
      (by norm_num : (1 / 4 : ℝ) ≤ 5 / 4))
    (by simpa only [norm_one, one_mul] using
      quadraticHeckePrincipalIdealNorm_summable F (σ := 5 / 4) (by norm_num)) (inv_pos.mpr hX)
  simp only [one_mul, div_inv_eq_mul, mul_comm (Ideal.absNorm _ : ℝ) X] at h
  have hInv (J : Ideals) :
      mellinInv (5 / 4) (quadraticHeckeDualMellin A r w) (X * (Ideal.absNorm J.val : ℝ)) =
        quadraticHeckeDualProfile A r w (X * (Ideal.absNorm J.val : ℝ)) := by
    rw [← quadraticHeckeDualProfileAt_eq_mellinInv, quadraticHeckeDualProfile]
    exact (quadraticHeckeDualProfileAt_eq A r w hcompact hpositive hsmooth
      (by norm_num) (by norm_num) (mul_pos hX (quadraticHeckePrincipalIdealNorm_pos F J))).symm
  simp_rw [hInv] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  change _ * _ * (∑' J : Ideals, ((Ideal.absNorm J.val : ℝ) : ℂ) ^ (-(L t))) = _
  rw [quadraticHeckePrincipalIdealSeries_eq_zeta F (by norm_num [L])]

theorem quadraticHeckePrincipalNormContour_left
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    verticalIntegral (-(1 / 4)) (quadraticHeckePrincipalIntegrand F w X) =
      (X : ℂ) * ∑' I : Ideals, quadraticHeckeDualProfile A r w (X * (Ideal.absNorm I.val : ℝ)) := by
  let L (t : ℝ) : ℂ := ((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I
  let left (t : ℝ) := quadraticHeckePrincipalIntegrand F w X
    (Complex.ofReal (-(1 / 4 : ℝ)) + (t : ℂ) * I)
  let right (t : ℝ) := ((X⁻¹ : ℝ) : ℂ) ^ L t * quadraticHeckeDualMellin A r w (L t) *
    dedekindZeta F (L t)
  have hflip : (∫ t : ℝ, left t) = (X : ℂ) * ∫ t : ℝ, right t := by
    calc
      _ = ∫ t : ℝ, left (-t) := (integral_neg_eq_self left volume).symm
      _ = ∫ t : ℝ, (X : ℂ) * right t := by
        apply integral_congr_ae
        filter_upwards with t
        have hr : Complex.ofReal (-(1 / 4 : ℝ)) + Complex.ofReal (-t) * I = 1 - L t := by
          dsimp [L]
          push_cast
          ring
        dsimp only [left, right]
        rw [hr]
        exact principalContour_reflect F w hX (L t) (by norm_num [L])
      _ = _ := integral_const_mul _ _
  rw [quadraticHeckePrincipalDualSeries_eq_integral F w hcompact hpositive hsmooth hX, verticalIntegral]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, left t) =
    (X : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, right t)
  rw [hflip]
  ring

/-- The principal norm Poisson formula with the actual zeta residue at one. -/
theorem quadraticHeckePrincipalNormPoisson
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    (∑' I : Ideals, w ((Ideal.absNorm I.val : ℝ) / X)) =
      (dedekindZeta_residue F : ℂ) * (X : ℂ) * mellin w 1 +
        (X : ℂ) * ∑' I : Ideals, quadraticHeckeDualProfile A r w (X * (Ideal.absNorm I.val : ℝ)) := by
  rw [quadraticHeckePrincipalNormContour_right F w hcompact hpositive hsmooth hX,
    quadraticHeckePrincipalNormContour_shift F w hcompact hpositive hsmooth hX,
    quadraticHeckePrincipalNormContour_left F w hcompact hpositive hsmooth hX, add_comm]

end
end ArtinMatthews
