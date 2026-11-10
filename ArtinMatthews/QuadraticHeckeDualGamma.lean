module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference


set_option backward.privateInPublic true
@[expose] public section

/-! The gamma ratio in the quadratic Hecke norm transform, specialized
to the totally complex fields used by the source. -/
namespace ArtinMatthews
open OAI.CubicReflectionKernel
open scoped Classical
noncomputable section

def quadraticHeckeDualGamma (A : ℝ) (r : ℕ) (s : ℂ) : ℂ :=
  Complex.exp ((2 * s - 1) * (Real.log A : ℂ)) *
    (Complex.Gamma s / Complex.Gamma (1 - s)) ^ r

theorem quadraticHeckeDualGamma_half (A : ℝ) (r : ℕ) :
    quadraticHeckeDualGamma A r (1 / 2) = 1 := by
  have hG : Complex.Gamma (1 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have h1 : (2 : ℂ) * (1 / 2) - 1 = 0 := by norm_num
  have h2 : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  rw [quadraticHeckeDualGamma, h1, zero_mul, Complex.exp_zero, h2, div_self hG, one_pow, one_mul]

theorem exists_quadraticHeckeDualGamma_strip_bound (A : ℝ) (r B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ (B : ℝ) + 1 / 2 →
      ‖quadraticHeckeDualGamma A r s‖ ≤ C * (1 + |s.im|) ^ ((2 * B + 2) * r) := by
  obtain ⟨C, hC, hb⟩ := Gamma_pair_strip_bound (1 / 2) (by norm_num) B
  let D : ℝ := (2 * (B : ℝ) + 1) * |Real.log A|
  refine ⟨Real.exp D * C ^ r, by positivity, ?_⟩
  intro s hs₀ hs₁
  let σ := s.re - 1 / 2
  have hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (B : ℝ) := ⟨by dsimp [σ]; linarith, by dsimp [σ]; linarith⟩
  have hz : ((1 / 2 : ℝ) : ℂ) + ((σ : ℂ) + s.im * Complex.I) = s := by
    calc
      _ = (s.re : ℂ) + s.im * Complex.I := by dsimp [σ]; push_cast; ring
      _ = s := Complex.re_add_im s
  have ho : ((1 / 2 : ℝ) : ℂ) - ((σ : ℂ) + s.im * Complex.I) = 1 - s := by
    calc
      _ = 1 - (((1 / 2 : ℝ) : ℂ) + ((σ : ℂ) + s.im * Complex.I)) := by push_cast; ring
      _ = _ := congrArg (fun z : ℂ => 1 - z) hz
  have hRatio := hb σ hσ s.im
  rw [hz, ho] at hRatio
  have hAbs : |2 * s.re - 1| ≤ 2 * (B : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) B]
  have hReal : ((2 * s - 1) * (Real.log A : ℂ)).re ≤ D := by
    have he : ((2 * s - 1) * (Real.log A : ℂ)).re = (2 * s.re - 1) * Real.log A := by
      norm_num [Complex.mul_re, Complex.sub_re]
    rw [he]
    calc
      _ ≤ |(2 * s.re - 1) * Real.log A| := le_abs_self _
      _ = |2 * s.re - 1| * |Real.log A| := abs_mul _ _
      _ ≤ D := mul_le_mul_of_nonneg_right hAbs (abs_nonneg _)
  rw [quadraticHeckeDualGamma, norm_mul, Complex.norm_exp, norm_pow]
  calc
    _ ≤ Real.exp D * (C * (1 + |s.im|) ^ (2 * B + 2)) ^ r :=
      mul_le_mul (Real.exp_le_exp.mpr hReal)
        (pow_le_pow_left₀ (norm_nonneg _) hRatio _) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul, mul_assoc]

end
end ArtinMatthews
