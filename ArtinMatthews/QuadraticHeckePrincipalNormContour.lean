module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaZero
public import OAI.NumberTheory.DirichletL.Detector.Physical
public import ArtinMatthews.PrincipalDedekindProbeGrowth
public import ArtinMatthews.SourcePrincipalSimplePoleShift
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set VaryingKummerAnalytic SourcePhysical
open OAI.SevenEighths.ProbePhysical
open scoped ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]

def quadraticHeckePrincipalIntegrand (w : ℝ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  (X : ℂ) ^ s * mellin w s * mixedDedekindZeta F s

private def principalNumerator (w : ℝ → ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  (X : ℂ) ^ s * mellin w s * principalDedekindRegularized F s

private theorem principalIntegrand_strip_height (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    ∃ C : ℝ, ∀ s : ℂ, -(1 / 4 : ℝ) ≤ s.re → s.re ≤ 5 / 4 → 1 / 4 ≤ ‖s - 1‖ →
      ‖quadraticHeckePrincipalIntegrand F w X s‖ ≤ C * sourceContourHeightWeight s.im := by
  obtain ⟨C, m, hC, hzeta⟩ := exists_mixedDedekindZeta_strip_bound_away_pole F
  obtain ⟨B, _hB, hmellin⟩ :=
    smoothMellin_strip_decay w hcompact hpositive hsmooth (-(1 / 4)) (5 / 4) (m + 2)
  let D := max (X ^ (-(1 / 4 : ℝ))) (X ^ (5 / 4 : ℝ))
  have hD : 0 ≤ D := (Real.rpow_nonneg hX.le _).trans (le_max_left _ _)
  refine ⟨D * (C / (1 / 4)) * (2 ^ m * B), fun s hlo hhi hdist => ?_⟩
  have hXpow : ‖(X : ℂ) ^ s‖ ≤ D := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    rcases le_total X 1 with h | h
    · exact (Real.rpow_le_rpow_of_exponent_ge hX h hlo).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le h hhi).trans (le_max_right _ _)
  have hZ := hzeta (1 / 4) (by norm_num) s hlo hhi hdist
  have hM := sourceContourHeightWeight_of_rapid m s.im B ‖mellin w s‖
    (norm_nonneg _) (hmellin s hlo hhi)
  rw [quadraticHeckePrincipalIntegrand, norm_mul, norm_mul]
  calc
    _ ≤ D * ‖mellin w s‖ * (C / (1 / 4) * (|s.im| + 2) ^ m) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hXpow (norm_nonneg _)) hZ
        (norm_nonneg _) (mul_nonneg hD (norm_nonneg _))
    _ = (D * (C / (1 / 4))) * ((|s.im| + 2) ^ m * ‖mellin w s‖) := by ring
    _ ≤ (D * (C / (1 / 4))) * ((2 ^ m * B) * sourceContourHeightWeight s.im) :=
      mul_le_mul_of_nonneg_left hM (mul_nonneg hD (div_nonneg hC.le (by norm_num)))
    _ = _ := by ring

/-- The contour displacement meets only the genuine pole of the Dedekind zeta function. -/
theorem quadraticHeckePrincipalNormContour_shift (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) {X : ℝ} (hX : 0 < X) :
    verticalIntegral (5 / 4) (quadraticHeckePrincipalIntegrand F w X) =
      verticalIntegral (-(1 / 4)) (quadraticHeckePrincipalIntegrand F w X) +
        (dedekindZeta_residue F : ℂ) * (X : ℂ) * mellin w 1 := by
  obtain ⟨C, hbound⟩ := principalIntegrand_strip_height F w hcompact hpositive hsmooth hX
  have hEntire : Differentiable ℂ (principalNumerator F w X) :=
    ((differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).mul
      (smoothMellin_entire w hcompact hpositive hsmooth.continuous)).mul
        (principalDedekindRegularized_entire F)
  have hratio (s : ℂ) (hs : s ≠ (1 : ℂ)) :
      quadraticHeckePrincipalIntegrand F w X s = principalNumerator F w X s / (s - 1) := by
    rw [principalNumerator, principalDedekindRegularized_eq_zeta F hs,
      quadraticHeckePrincipalIntegrand]
    field_simp [sub_ne_zero.mpr hs]
  have hline (a : ℝ) (hlo : -(1 / 4 : ℝ) ≤ a) (hhi : a ≤ 5 / 4) (t : ℝ)
      (hdist : 1 / 4 ≤ |a - 1| ∨ 1 ≤ |t|) :
      ‖quadraticHeckePrincipalIntegrand F w X ((a : ℂ) + (t : ℂ) * I)‖ ≤
        C * sourceContourHeightWeight t := by
    have hdist' : 1 / 4 ≤ ‖((a : ℂ) + (t : ℂ) * I) - 1‖ := by
      rcases hdist with h | h
      · exact h.trans (by simpa using Complex.abs_re_le_norm (((a : ℂ) + (t : ℂ) * I) - 1))
      · have ht : |t| ≤ ‖((a : ℂ) + (t : ℂ) * I) - 1‖ := by
          simpa using Complex.abs_im_le_norm (((a : ℂ) + (t : ℂ) * I) - 1)
        exact (show (1 / 4 : ℝ) ≤ 1 by norm_num).trans (h.trans ht)
    simpa using hbound ((a : ℂ) + (t : ℂ) * I) (by simpa using hlo) (by simpa using hhi) hdist'
  have hshift := source_verticalIntegral_simple_pole_of_heightWeight
    (principalNumerator F w X) (quadraticHeckePrincipalIntegrand F w X)
    (a := -(1 / 4)) (b := 5 / 4) (p := 1) (C := C)
    (by norm_num) (by norm_num) hEntire.differentiableOn
    (fun s _ _ hs => hratio s (by simpa using hs))
    (fun t => hline _ le_rfl (by norm_num) t (Or.inl (by norm_num)))
    (fun t => hline _ (by norm_num) le_rfl t (Or.inl (by norm_num)))
    (fun a ha t ht => hline a ha.1 ha.2 t (Or.inr ht))
  simpa [principalNumerator, principalDedekindRegularized_one, mul_comm, mul_left_comm, mul_assoc]
    using hshift

end
end ArtinMatthews
