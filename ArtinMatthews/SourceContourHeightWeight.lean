module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import OAI.NumberTheory.DirichletL.ContinuationContour


set_option backward.privateInPublic true
@[expose] public section

/-! Inverse-quadratic height estimates for the actual contour shifts.
The horizontal limits are taken through the proved Cauchy rectangle
identity. The translated Gaussian is kept until a height is fixed. -/
namespace ArtinMatthews.SourcePhysical
open Filter MeasureTheory Set Complex OAI.SevenEighths.Continuation
open scoped Topology
noncomputable section

def sourceContourHeightWeight (t : ℝ) : ℝ := (1+t^2)⁻¹

theorem sourceContourHeightWeight_nonneg (t : ℝ) : 0 ≤ sourceContourHeightWeight t := by
  unfold sourceContourHeightWeight
  positivity

theorem sourceContourHeightWeight_le_one (t : ℝ) : sourceContourHeightWeight t ≤ 1 := by
  rw [sourceContourHeightWeight, ← one_div]
  exact (div_le_one (by positivity)).mpr (by linarith [sq_nonneg t])

theorem sourceContourHeightWeight_integrable : Integrable sourceContourHeightWeight :=
  integrable_inv_one_add_sq

theorem sourceContourHeightWeight_tendsto : Tendsto sourceContourHeightWeight atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)))

theorem sourceContourHeightWeight_neg (t : ℝ) : sourceContourHeightWeight (-t) = sourceContourHeightWeight t := by
  simp [sourceContourHeightWeight]

theorem sourceGaussian_translate_le_heightWeight (y t : ℝ) :
    Real.exp (-((y+t)^2)) ≤ 2*(1+t^2)*sourceContourHeightWeight y := by
  have h := Real.add_one_le_exp ((y+t)^2)
  have hG : Real.exp (-((y+t)^2))*(1+(y+t)^2) ≤ 1 := by
    calc
      _ ≤ Real.exp (-((y+t)^2))*Real.exp ((y+t)^2) :=
        mul_le_mul_of_nonneg_left (by linarith only [h]) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hQ : 1+y^2 ≤ (2*(1+t^2))*(1+(y+t)^2) := by
    nlinarith [sq_nonneg (y+2*t), mul_nonneg (sq_nonneg t) (sq_nonneg (y+t))]
  rw [sourceContourHeightWeight, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ Real.exp (-((y+t)^2))*((2*(1+t^2))*(1+(y+t)^2)) :=
      mul_le_mul_of_nonneg_left hQ (Real.exp_nonneg _)
    _ = (2*(1+t^2))*(Real.exp (-((y+t)^2))*(1+(y+t)^2)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hG

theorem sourceContourHeightWeight_of_rapid (m : ℕ) (t B R : ℝ) (hR : 0 ≤ R)
    (h : (1+|t|)^(m+2)*R ≤ B) :
    (|t|+2)^m*R ≤ ((2 : ℝ)^m*B)*sourceContourHeightWeight t := by
  have hp : (|t|+2)^m ≤ (2 : ℝ)^m*(1+|t|)^m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg t]) m
  have hsq : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t, abs_nonneg t]
  rw [sourceContourHeightWeight, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ (((2 : ℝ)^m*(1+|t|)^m)*R)*((1+|t|)^2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hp hR) hsq (by positivity) (by positivity)
    _ = (2 : ℝ)^m*((1+|t|)^(m+2)*R) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

/-- Cauchy's theorem with a uniform, integrable inverse-quadratic bound. -/
theorem source_vertical_integral_eq_of_heightWeight (f : ℂ → ℂ) {a b C : ℝ}
    (hab : a ≤ b) (hhol : DifferentiableOn ℂ f {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ, ‖f ((x : ℂ)+y*I)‖ ≤ C*sourceContourHeightWeight y) :
    (∫ y : ℝ, f ((a : ℂ)+y*I)) = ∫ y : ℝ, f ((b : ℂ)+y*I) := by
  have hV (x : ℝ) (hx : x ∈ Icc a b) : Integrable (fun y : ℝ => f ((x : ℂ)+y*I)) := by
    have hc : Continuous (fun y : ℝ => f ((x : ℂ)+y*I)) :=
      hhol.continuousOn.comp_continuous (by fun_prop) (fun y => by simpa using hx)
    exact (sourceContourHeightWeight_integrable.const_mul C).mono' hc.aestronglyMeasurable
      (ae_of_all _ (hbound x hx))
  have hSide (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
      Tendsto (fun y : ℝ => ∫ x in a..b, f ((x : ℂ)+(sign*y : ℝ)*I)) atTop (𝓝 0) := by
    have hN (y : ℝ) : ‖∫ x in a..b, f ((x : ℂ)+(sign*y : ℝ)*I)‖ ≤
        (C*sourceContourHeightWeight y)*|b-a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hx
      rcases hsign with rfl | rfl
      · simpa only [one_mul] using hbound x hx' y
      · simpa only [neg_one_mul, sourceContourHeightWeight_neg] using hbound x hx' (-y)
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hN
      (by simpa using (sourceContourHeightWeight_tendsto.const_mul C).mul_const |b-a|)
  apply vertical_integral_eq_of_horizontal_vanish f hab hhol (hV a ⟨le_rfl,hab⟩) (hV b ⟨hab,le_rfl⟩)
  · simpa only [neg_one_mul, Complex.ofReal_neg] using hSide (-1) (Or.inr rfl)
  · simpa only [one_mul] using hSide 1 (Or.inl rfl)

end
end ArtinMatthews.SourcePhysical
