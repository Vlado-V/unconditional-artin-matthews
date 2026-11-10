module

public import ArtinMatthews.QuadraticHeckeSquareMellin
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaZero
public import OAI.NumberTheory.DirichletL.Detector.Physical
public import ArtinMatthews.QuadraticHeckeNormSmoothing
public import ArtinMatthews.QuadraticHeckePositivePrincipalShift
public import ArtinMatthews.QuadraticHeckePrincipalNormSeries
public import ArtinMatthews.SourceQuadraticPoissonErrorMellin
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

namespace ArtinMatthews
open NumberField Complex Set MeasureTheory VaryingKummerAnalytic SourcePhysical
open OAI.SevenEighths.ProbePhysical
open scoped NumberField ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (A : ℝ) (r : ℕ) (w : ℝ → ℂ)

theorem quadraticHeckeDualSquareMellin_differentiableAt
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {s : ℂ} (h : 0 < s.re) :
    DifferentiableAt ℂ (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) s := by
  have hd := quadraticHeckeDualMellin_differentiableAt A r w hc hp hs.continuous
    (s / 2) (by simpa only [div_ofNat_re] using half_pos h)
  exact (hd.comp s ((differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) s).div_const
    (2 : ℂ))).const_mul (1 / 2 : ℂ)

theorem quadraticHeckeDualSquareMellin_strip_decay
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    (u v : ℝ) (hu : 0 < u) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      (1 + |s.im|) ^ k *
        ‖quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w) s‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := quadraticHeckeDualMellin_strip_decay_pos A r w hc hp hs
    (u / 2) (v / 2) (half_pos hu) k
  refine ⟨2 ^ k * C, by positivity, ?_⟩
  intro s hlo hhi
  have hhalf := hb (s / 2) (by simp only [div_ofNat_re]; linarith)
    (by simp only [div_ofNat_re]; linarith)
  rw [div_ofNat_im] at hhalf
  have ht : 1 + |s.im| ≤ 2 * (1 + |s.im / 2|) := by
    rw [abs_div]
    norm_num
    linarith [abs_nonneg s.im]
  have hn : ‖quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w) s‖ ≤
      ‖quadraticHeckeDualMellin A r w (s / 2)‖ := by
    rw [quadraticHeckeSquareMellin, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by norm_num)
  calc
    _ ≤ (2 * (1 + |s.im / 2|)) ^ k * ‖quadraticHeckeDualMellin A r w (s / 2)‖ :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) ht _) hn (norm_nonneg _) (by positivity)
    _ = 2 ^ k * ((1 + |s.im / 2|) ^ k * ‖quadraticHeckeDualMellin A r w (s / 2)‖) := by
      rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hhalf (by positivity)

/-- The noncompact dual square profile is represented by the genuine principal
ideal Dirichlet series on its absolutely convergent line. -/
theorem quadraticHeckeDualSquareNormContour_right
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {X : ℝ} (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      quadraticHeckeDualProfile A r w (((Ideal.absNorm J.val : ℝ) / X) ^ 2)) =
      verticalIntegral (5 / 4) (fun s : ℂ => (X : ℂ) ^ s *
        quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w) s *
          mixedDedekindZeta F s) := by
  let : Countable {J : Ideal (𝓞 F) // J ≠ ⊥} := quadraticHeckePrincipalIdeal_countable F
  have hcont : Continuous (fun t : ℝ =>
      quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)
        (((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (quadraticHeckeDualSquareMellin_differentiableAt A r w hc hp hs
      (by norm_num)).continuousAt.comp' (f := fun t : ℝ => ((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I)
        (x := t) (by fun_prop)
  have h := quadraticHeckeNormSmoothing_contour
    (fun J : {J : Ideal (𝓞 F) // J ≠ ⊥} => (Ideal.absNorm J.val : ℝ))
    (quadraticHeckePrincipalIdealNorm_pos F) (fun _ => 1)
    (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) (5 / 4) hcont
    (by simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
      quadraticHeckeSquareMellin_dual_verticalIntegrable A r w hc hp hs)
    (by simpa only [norm_one, one_mul] using
      quadraticHeckePrincipalIdealNorm_summable F (σ := 5 / 4) (by norm_num)) hX
  simp only [one_mul] at h
  have hinv (J : {J : Ideal (𝓞 F) // J ≠ ⊥}) :=
    quadraticHeckeSquareMellin_dual_inversion A r w hc hp hs
      (div_pos (quadraticHeckePrincipalIdealNorm_pos F J) hX)
  simp_rw [hinv] at h
  rw [h, verticalIntegral]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  let s : ℂ := ((5 / 4 : ℝ) : ℂ) + (t : ℂ) * I
  have hs' : 1 < s.re := by norm_num [s]
  change _ * _ * (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      ((Ideal.absNorm J.val : ℝ) : ℂ) ^ (-s)) = _ * _ * mixedDedekindZeta F s
  rw [quadraticHeckePrincipalIdealSeries_eq_zeta F hs', mixedDedekindZeta_eq F hs']

/-- Shift the actual dual square norm sum to any positive line below one.
Its residue is exactly the half-Mellin moment of the original compact weight. -/
theorem quadraticHeckeDualSquareNormContour_shift
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ X : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hX : 0 < X) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      quadraticHeckeDualProfile A r w (((Ideal.absNorm J.val : ℝ) / X) ^ 2)) =
      verticalIntegral σ (fun s : ℂ => (X : ℂ) ^ s *
        quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w) s *
          mixedDedekindZeta F s) +
        (dedekindZeta_residue F : ℂ) * (X : ℂ) * ((1 / 2 : ℂ) * mellin w (1 / 2)) := by
  rw [quadraticHeckeDualSquareNormContour_right F A r w hc hp hs hX]
  have h := quadraticHeckePositivePrincipalShift F
    (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) hσ₀ hσ₁ hX
    (fun s h => (quadraticHeckeDualSquareMellin_differentiableAt A r w hc hp hs
      (hσ₀.trans_le h.1)).differentiableWithinAt)
    (quadraticHeckeDualSquareMellin_strip_decay A r w hc hp hs σ (5 / 4) hσ₀)
  dsimp only at h
  rw [quadraticHeckeSquareMellin_dual_half_eq] at h
  exact h

end
end ArtinMatthews
