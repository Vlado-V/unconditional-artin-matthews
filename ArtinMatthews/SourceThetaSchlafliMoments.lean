module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Positive Schläfli monomial moments for the literal cubic Bessel
factor. The exponential series bounds every polynomial insertion. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Filter
noncomputable section

def sourceThetaSchlafliPhase (scale x z : ℝ) : ℝ :=
  scale * Real.exp x / z

def sourceThetaSchlafliMomentIntegrand (scale : ℝ) (k : ℕ) (x z : ℝ) : ℝ :=
  Real.exp ((5 / 6 : ℝ) * x) * (z ^ (-(2 / 3 : ℝ)) *
    (sourceThetaSchlafliPhase scale x z ^ k * Real.exp (-z - sourceThetaSchlafliPhase scale x z)))

def sourceThetaSchlafliMoment (scale : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∫ z in Ioi 0, sourceThetaSchlafliMomentIntegrand scale k x z

def sourceThetaSchlafliGammaDensity (N : ℕ) (z : ℝ) : ℝ :=
  z ^ ((N : ℝ) - 2 / 3) * Real.exp (-z)

theorem sourceThetaSchlafliGammaDensity_integrable (N : ℕ) :
    IntegrableOn (sourceThetaSchlafliGammaDensity N) (Ioi 0) := by
  change IntegrableOn (fun z : ℝ => z ^ ((N : ℝ) - 2 / 3) * Real.exp (-z)) (Ioi 0)
  have h := Real.GammaIntegral_convergent (s := (N : ℝ) + 1 / 3) (by positivity)
  simpa only [mul_comm,
    show (N : ℝ) + 1 / 3 - 1 = (N : ℝ) - 2 / 3 by ring] using h

theorem sourceThetaSchlafliMomentIntegrand_measurable (scale : ℝ) (k : ℕ) (x : ℝ) :
    Measurable (sourceThetaSchlafliMomentIntegrand scale k x) := by
  unfold sourceThetaSchlafliMomentIntegrand sourceThetaSchlafliPhase
  fun_prop

theorem sourceThetaSchlafliMomentIntegrand_pos {scale z : ℝ} (hscale : 0 < scale) (hz : 0 < z)
    (k : ℕ) (x : ℝ) : 0 < sourceThetaSchlafliMomentIntegrand scale k x z := by
  unfold sourceThetaSchlafliMomentIntegrand sourceThetaSchlafliPhase
  positivity

private theorem thetaPow_exp_neg_le_factorial {y : ℝ} (hy : 0 < y) (k N : ℕ) :
    y ^ k * Real.exp (-y) ≤ ((k + N).factorial : ℝ) / y ^ N := by
  have hf : 0 < ((k + N).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp y hy.le (k + N))
  apply (le_div_iff₀ (pow_pos hy N)).mpr
  calc
    _ = y ^ (k + N) * Real.exp (-y) := by rw [pow_add]; ring
    _ ≤ (Real.exp y * (↑(k + N).factorial : ℝ)) * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_neg]; field_simp [Real.exp_ne_zero y]

private theorem thetaSchlafli_coefficient (scale x D : ℝ) (N : ℕ) :
    Real.exp ((5 / 6 : ℝ) * x) * (D / (scale * Real.exp x) ^ N) =
      (D / scale ^ N) * Real.exp (((5 / 6 : ℝ) - N) * x) := by
  rw [mul_pow, div_mul_eq_div_div, ← Real.exp_nat_mul]
  calc
    _ = (D / scale ^ N) * (Real.exp ((5 / 6 : ℝ) * x) * Real.exp (-((N : ℝ) * x))) := by
      rw [Real.exp_neg, div_eq_mul_inv (D / scale ^ N)]
      ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem sourceThetaSchlafliMomentIntegrand_le {scale z : ℝ} (hscale : 0 < scale) (hz : 0 < z)
    (k N : ℕ) (x : ℝ) :
    sourceThetaSchlafliMomentIntegrand scale k x z ≤
      (((k + N).factorial : ℝ) / scale ^ N * Real.exp (((5 / 6 : ℝ) - N) * x)) *
        sourceThetaSchlafliGammaDensity N z := by
  let y := sourceThetaSchlafliPhase scale x z
  have hy : 0 < y := by dsimp only [y, sourceThetaSchlafliPhase]; positivity
  have hpow : z ^ (-(2 / 3 : ℝ)) * z ^ N = z ^ ((N : ℝ) - 2 / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hz]
    congr 1
    ring
  calc
    _ = (Real.exp ((5 / 6 : ℝ) * x) * z ^ (-(2 / 3 : ℝ)) * Real.exp (-z)) *
        (y ^ k * Real.exp (-y)) := by
      change Real.exp ((5 / 6 : ℝ) * x) * (z ^ (-(2 / 3 : ℝ)) * (y ^ k * Real.exp (-z - y))) = _
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ (Real.exp ((5 / 6 : ℝ) * x) * z ^ (-(2 / 3 : ℝ)) * Real.exp (-z)) *
        (((k + N).factorial : ℝ) / y ^ N) :=
      mul_le_mul_of_nonneg_left (thetaPow_exp_neg_le_factorial hy k N) (by positivity)
    _ = _ := by
      dsimp only [y, sourceThetaSchlafliPhase, sourceThetaSchlafliGammaDensity]
      rw [div_pow, div_div_eq_mul_div, ← thetaSchlafli_coefficient, ← hpow]
      ring

theorem sourceThetaSchlafliMomentIntegrand_integrable {scale : ℝ} (hscale : 0 < scale)
    (k : ℕ) (x : ℝ) :
    IntegrableOn (sourceThetaSchlafliMomentIntegrand scale k x) (Ioi 0) := by
  apply ((sourceThetaSchlafliGammaDensity_integrable 0).const_mul
    (((k + 0).factorial : ℝ) / scale ^ (0 : ℕ) * Real.exp (((5 / 6 : ℝ) - (0 : ℕ)) * x))).mono'
    (sourceThetaSchlafliMomentIntegrand_measurable scale k x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [Real.norm_of_nonneg (sourceThetaSchlafliMomentIntegrand_pos hscale hz k x).le]
  exact sourceThetaSchlafliMomentIntegrand_le hscale hz k 0 x

theorem sourceThetaSchlafliMoment_pos {scale : ℝ} (hscale : 0 < scale) (k : ℕ) (x : ℝ) :
    0 < sourceThetaSchlafliMoment scale k x := by
  unfold sourceThetaSchlafliMoment
  rw [setIntegral_pos_iff_support_of_nonneg_ae ?_ (sourceThetaSchlafliMomentIntegrand_integrable hscale k x)]
  · rw [inter_eq_self_of_subset_right]
    · exact isOpen_Ioi.measure_pos volume (nonempty_Ioi : (Ioi (0 : ℝ)).Nonempty)
    · intro z hz
      exact (sourceThetaSchlafliMomentIntegrand_pos hscale hz k x).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact (sourceThetaSchlafliMomentIntegrand_pos hscale hz k x).le

theorem sourceThetaSchlafliMoment_weighted {scale : ℝ} (hscale : 0 < scale) (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖sourceThetaSchlafliMoment scale k x‖ ≤ C * Real.exp (((5 / 6 : ℝ) - N) * x) := by
  let D := ((k + N).factorial : ℝ) / scale ^ N
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hΓ : 0 ≤ (∫ z in Ioi 0, sourceThetaSchlafliGammaDensity N z) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le
  refine ⟨D * (∫ z in Ioi 0, sourceThetaSchlafliGammaDensity N z), mul_nonneg hD hΓ, fun x => ?_⟩
  rw [Real.norm_of_nonneg (sourceThetaSchlafliMoment_pos hscale k x).le, sourceThetaSchlafliMoment]
  calc
    _ ≤ ∫ z in Ioi 0, (D * Real.exp (((5 / 6 : ℝ) - N) * x)) * sourceThetaSchlafliGammaDensity N z := by
      apply integral_mono_ae (sourceThetaSchlafliMomentIntegrand_integrable hscale k x)
        ((sourceThetaSchlafliGammaDensity_integrable N).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact sourceThetaSchlafliMomentIntegrand_le hscale hz k N x
    _ = _ := by rw [integral_const_mul]; ac_rfl

end
end ArtinMatthews.SourceReflection
