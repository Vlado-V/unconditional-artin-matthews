module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp


set_option backward.privateInPublic true
@[expose] public section

/-! Fourier separation in one actual finite column dyad. The retained
cutoff is part of the column vector, and the row norm is the literal
finite Euclidean norm. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

/-- Unit-frequency convention of the source inverse Fourier integral. -/
def sourceReflectedFourierPhase (τ x : ℝ) : ℂ := Complex.exp (Complex.I * ((τ * x : ℝ) : ℂ))

theorem sourceReflectedFourierPhase_norm (τ x : ℝ) : ‖sourceReflectedFourierPhase τ x‖ = 1 := by
  simp [sourceReflectedFourierPhase, Complex.norm_exp, Complex.mul_re]

theorem sourceReflectedFourierPhase_add (τ x y : ℝ) :
    sourceReflectedFourierPhase τ (x + y) =
      sourceReflectedFourierPhase τ x * sourceReflectedFourierPhase τ y := by
  unfold sourceReflectedFourierPhase
  rw [mul_add τ, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem sourceReflectedFourierPhase_continuous (x : ℝ) :
    Continuous (fun τ : ℝ => sourceReflectedFourierPhase τ x) := by
  unfold sourceReflectedFourierPhase
  fun_prop

/-- Integrate the actual row and column phase separation against an
integrable Fourier coefficient. Finite-dimensional Minkowski costs only
its L¹ norm, with the very same sieve constant at every frequency. -/
theorem source_fourier_separated_column_energy {Rows Cols : Type*} [Fintype Rows] [Fintype Cols]
    (K : Rows → Cols → ℂ) {U : ℝ} (hU : 0 ≤ U)
    (hK : ∀ b : Cols → ℂ, (∑ i, ‖∑ j, K i j * b j‖ ^ 2) ≤ U ^ 2 * ∑ j, ‖b j‖ ^ 2)
    (r : Rows → ℂ) (hr : ∀ i, ‖r i‖ ≤ 1) (a : Cols → ℂ)
    (u : Rows → ℝ) (v : Cols → ℝ) (g : ℝ → ℂ) (hg : Integrable g) :
    Real.sqrt (∑ i, ‖∑ j, r i * K i j * a j *
      (∫ τ : ℝ, g τ * sourceReflectedFourierPhase τ (u i + v j))‖ ^ 2) ≤
      (∫ τ : ℝ, ‖g τ‖) * U * Real.sqrt (∑ j, ‖a j‖ ^ 2) := by
  classical
  let b (τ : ℝ) (j : Cols) := a j * sourceReflectedFourierPhase τ (v j)
  let W (τ : ℝ) : EuclideanSpace ℂ Rows := WithLp.toLp 2
    (fun i => r i * sourceReflectedFourierPhase τ (u i) * ∑ j, K i j * b τ j)
  let G (τ : ℝ) : EuclideanSpace ℂ Rows := g τ • W τ
  have hW (τ : ℝ) : ‖W τ‖ ≤ U * Real.sqrt (∑ j, ‖a j‖ ^ 2) := by
    have hb (j : Cols) : ‖b τ j‖ = ‖a j‖ := by
      rw [show b τ j = a j * sourceReflectedFourierPhase τ (v j) from rfl,
        norm_mul, sourceReflectedFourierPhase_norm, mul_one]
    have hw (i : Rows) : ‖W τ i‖ ^ 2 ≤ ‖∑ j, K i j * b τ j‖ ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      change ‖r i * sourceReflectedFourierPhase τ (u i) * ∑ j, K i j * b τ j‖ ≤ _
      rw [norm_mul, norm_mul, sourceReflectedFourierPhase_norm, mul_one]
      exact (mul_le_mul_of_nonneg_right (hr i) (norm_nonneg _)).trans_eq (one_mul _)
    have hsq := (Finset.sum_le_sum (fun i _ => hw i)).trans (hK (b τ))
    simp only [hb] at hsq
    rw [EuclideanSpace.norm_eq]
    exact (Real.sqrt_le_sqrt hsq).trans_eq (by rw [Real.sqrt_mul (sq_nonneg U), Real.sqrt_sq hU])
  have hterm (i : Rows) (j : Cols) : Integrable (fun τ : ℝ => g τ *
      sourceReflectedFourierPhase τ (u i + v j)) :=
    hg.mul_bdd ((sourceReflectedFourierPhase_continuous (u i + v j)).aestronglyMeasurable)
      (c := 1) (Filter.Eventually.of_forall fun τ => (sourceReflectedFourierPhase_norm τ _).le)
  have hGi (i : Rows) (τ : ℝ) : G τ i = ∑ j, (r i * K i j * a j) *
      (g τ * sourceReflectedFourierPhase τ (u i + v j)) := by
    change g τ * (r i * sourceReflectedFourierPhase τ (u i) * ∑ j, K i j * b τ j) = _
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [sourceReflectedFourierPhase_add]
    dsimp only [b]
    ring
  have hGiInt (i : Rows) : Integrable (fun τ : ℝ => G τ i) := by
    simp_rw [hGi]
    exact integrable_finsetSum _ (fun j _ => (hterm i j).const_mul _)
  have hG : Integrable G := Integrable.of_eval_piLp hGiInt
  have hcoord (i : Rows) : (∫ τ : ℝ, G τ) i = ∑ j, r i * K i j * a j *
      (∫ τ : ℝ, g τ * sourceReflectedFourierPhase τ (u i + v j)) := by
    rw [eval_integral_piLp hGiInt]
    simp_rw [hGi]
    rw [integral_finsetSum _ (fun j _ => (hterm i j).const_mul _)]
    simp_rw [integral_const_mul]
  calc
    _ = ‖∫ τ : ℝ, G τ‖ := by rw [EuclideanSpace.norm_eq]; simp only [hcoord]
    _ ≤ ∫ τ : ℝ, ‖G τ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ τ : ℝ, ‖g τ‖ * (U * Real.sqrt (∑ j, ‖a j‖ ^ 2)) := by
      apply integral_mono hG.norm (hg.norm.mul_const _)
      intro τ
      change ‖g τ • W τ‖ ≤ ‖g τ‖ * (U * Real.sqrt (∑ j, ‖a j‖ ^ 2))
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hW τ) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const, mul_assoc]

end
end ArtinMatthews.SourceReflection
