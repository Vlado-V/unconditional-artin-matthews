module

public import ArtinMatthews.QuadraticHeckeDualGamma
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.MellinTransform
public import ArtinMatthews.VaryingKummerAnalyticSmoothMellin
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open VaryingKummerAnalytic MeasureTheory
open scoped ContDiff
noncomputable section

/-- The totally complex quadratic Hecke dual Mellin symbol, in the
normalization where the conductor is kept outside the fixed profile. -/
def quadraticHeckeDualMellin (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (s : ℂ) : ℂ :=
  quadraticHeckeDualGamma A r s * mellin w (1 - s)

theorem quadraticHeckeDualMellin_half (A : ℝ) (r : ℕ) (w : ℝ → ℂ) :
    quadraticHeckeDualMellin A r w (1 / 2) = mellin w (1 / 2) := by
  rw [quadraticHeckeDualMellin, quadraticHeckeDualGamma_half, one_mul]
  congr 1
  ring

theorem quadraticHeckeDualGamma_differentiableAt (A : ℝ) (r : ℕ) (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (quadraticHeckeDualGamma A r) s := by
  have hG : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma _ (by
    intro n hn
    have hn' := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at hn'
    linarith [Nat.cast_nonneg (α := ℝ) n])
  have h₁ : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
  have hinv : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gamma (1 - z))⁻¹) s :=
    Complex.differentiable_one_div_Gamma.differentiableAt.comp s
      h₁
  have hE : DifferentiableAt ℂ (fun z : ℂ =>
      Complex.exp ((2 * z - 1) * (Real.log A : ℂ))) s := by fun_prop
  unfold quadraticHeckeDualGamma
  simp only [div_eq_mul_inv]
  exact hE.mul ((hG.mul hinv).pow r)

theorem quadraticHeckeDualMellin_differentiableAt (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Set.Ioi 0)
    (hcontinuous : Continuous w) (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (quadraticHeckeDualMellin A r w) s := by
  have h₁ : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
  exact (quadraticHeckeDualGamma_differentiableAt A r s hs).mul
    ((smoothMellin_entire w hcompact hpositive hcontinuous).differentiableAt.comp s h₁)

theorem quadraticHeckeDualMellin_strip_decay (A : ℝ) (r B : ℕ) (w : ℝ → ℂ)
    (hcompact : HasCompactSupport w) (hpositive : tsupport w ⊆ Set.Ioi 0)
    (hsmooth : ContDiff ℝ ∞ w) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ (B : ℝ) + 1 / 2 →
      (1 + |s.im|) ^ k * ‖quadraticHeckeDualMellin A r w s‖ ≤ C := by
  let n : ℕ := (2 * B + 2) * r
  obtain ⟨Cγ, hCγ, hγ⟩ := exists_quadraticHeckeDualGamma_strip_bound A r B
  obtain ⟨Cw, hCw, hw⟩ := smoothMellin_strip_decay w hcompact hpositive hsmooth
    ((1 / 2 : ℝ) - B) (3 / 4) (k + n)
  refine ⟨Cγ * Cw, mul_pos hCγ hCw, ?_⟩
  intro s hlo hhi
  have hm := hw (1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hm
  let T : ℝ := 1 + |s.im|
  have hT : 0 < T := by dsimp [T]; positivity
  rw [quadraticHeckeDualMellin, norm_mul]
  calc
    _ ≤ T ^ k * ((Cγ * T ^ n) * ‖mellin w (1 - s)‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hγ s hlo hhi) (norm_nonneg _)) (pow_nonneg hT.le _)
    _ = Cγ * (T ^ (k + n) * ‖mellin w (1 - s)‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm hCγ.le

end
end ArtinMatthews
