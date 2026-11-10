module

public import ArtinMatthews.SourceComplexMellinWeight
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import ArtinMatthews.SourceComplexZetaIntegrability
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped SchwartzMap
noncomputable section

def sourceComplexMellinMajorant (f : 𝓢(ℂ, ℂ)) (lo hi : ℝ) (z : ℂ) : ℝ :=
  ‖f z‖ * ‖z‖ ^ (-(max 0 (2 - 2 * lo))) +
    ‖z‖ ^ Nat.ceil (max 0 (2 * hi - 2)) * ‖f z‖

theorem sourceComplexMellinMajorant_integrable (f : 𝓢(ℂ, ℂ)) (lo hi : ℝ) (hlo : 0 < lo) :
    Integrable (sourceComplexMellinMajorant f lo hi) sourceComplexTraceMeasure := by
  have ha : max 0 (2 - 2 * lo) < 2 := max_lt_iff.mpr ⟨by norm_num, by linarith⟩
  have hn := (source_complex_schwartz_weighted_integrable f (max 0 (2 - 2 * lo))
    (le_max_left _ _) ha).norm
  have hn' : Integrable (fun z : ℂ => ‖f z‖ * ‖z‖ ^ (-(max 0 (2 - 2 * lo)))) := by
    apply hn.congr
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact (hn'.add (f.integrable_pow_mul volume _)).smul_measure
    (by norm_num : (2 : ENNReal) ≠ ⊤)

theorem sourceComplexMellin_integrand_norm_le (f : 𝓢(ℂ, ℂ)) (lo hi : ℝ) (s z : ℂ)
    (hl : lo ≤ s.re) (hh : s.re ≤ hi) (hz : z ≠ 0) :
    ‖f z * sourceComplexMellinWeight s z‖ ≤ sourceComplexMellinMajorant f lo hi z := by
  rw [norm_mul, sourceComplexMellinWeight_norm _ _ hz]
  unfold sourceComplexMellinMajorant
  by_cases hr : ‖z‖ ≤ 1
  · have he : -(max 0 (2 - 2 * lo)) ≤ 2 * s.re - 2 := by
      linarith [le_max_right (0 : ℝ) (2 - 2 * lo)]
    have hw := Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hz) hr he
    exact (mul_le_mul_of_nonneg_left hw (norm_nonneg _)).trans
      (le_add_of_nonneg_right (by positivity))
  · have he : 2 * s.re - 2 ≤ (Nat.ceil (max 0 (2 * hi - 2)) : ℝ) := by
      calc
        _ ≤ 2 * hi - 2 := by linarith
        _ ≤ max 0 (2 * hi - 2) := le_max_right _ _
        _ ≤ _ := Nat.le_ceil _
    have hw := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr) he
    rw [Real.rpow_natCast] at hw
    calc
      _ ≤ ‖f z‖ * ‖z‖ ^ Nat.ceil (max 0 (2 * hi - 2)) :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ = ‖z‖ ^ Nat.ceil (max 0 (2 * hi - 2)) * ‖f z‖ := mul_comm _ _
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

theorem sourceComplexMellin_integrable_of_band (f : 𝓢(ℂ, ℂ)) (lo hi : ℝ) (s : ℂ)
    (hlo : 0 < lo) (hl : lo ≤ s.re) (hh : s.re ≤ hi) :
    Integrable (fun z : ℂ => f z * sourceComplexMellinWeight s z) sourceComplexTraceMeasure := by
  apply (sourceComplexMellinMajorant_integrable f lo hi hlo).mono'
  · exact (f.continuous.measurable.mul (sourceComplexMellinWeight_measurable s)).aestronglyMeasurable
  · filter_upwards [sourceComplexTraceMeasure_ae_ne_zero] with z hz
    exact sourceComplexMellin_integrand_norm_le f lo hi s z hl hh hz

theorem sourceComplexMellin_integrable (f : 𝓢(ℂ, ℂ)) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun z : ℂ => f z * sourceComplexMellinWeight s z) sourceComplexTraceMeasure :=
  sourceComplexMellin_integrable_of_band f s.re s.re s hs le_rfl le_rfl

theorem sourceComplexMellin_norm_bound (f : 𝓢(ℂ, ℂ)) (lo hi : ℝ) (s : ℂ)
    (hlo : 0 < lo) (hl : lo ≤ s.re) (hh : s.re ≤ hi) :
    ‖sourceComplexMellin f s‖ ≤ ∫ z : ℂ, sourceComplexMellinMajorant f lo hi z ∂sourceComplexTraceMeasure := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (sourceComplexMellin_integrable_of_band f lo hi s hlo hl hh).norm
    (sourceComplexMellinMajorant_integrable f lo hi hlo)
  filter_upwards [sourceComplexTraceMeasure_ae_ne_zero] with z hz
  exact sourceComplexMellin_integrand_norm_le f lo hi s z hl hh hz

end
end ArtinMatthews.VaryingKummerAnalytic
