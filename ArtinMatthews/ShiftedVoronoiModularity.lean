module

public import Mathlib.NumberTheory.ModularForms.QExpansion


set_option backward.privateInPublic true
@[expose] public section

/-!
# The modular transformation underlying the weight-one Voronoi formula

We derive the rational-cusp transformation from an actual slash-invariant form.
No summation formula or modular transformation is assumed as a functional identity.
The matrix must belong to the form's invariance group. Identifying the cubic theta
series with such a form, and obtaining the general Bessel-transform summation
formula from this identity, are separate tasks.
-/

noncomputable section
open Complex UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

/-- A point at height `y` above a real number. -/
def cuspVerticalPoint (x y : ℝ) (hy : 0 < y) : ℍ :=
  ⟨(x : ℂ) + (y : ℂ) * Complex.I, by simpa using hy⟩

@[simp] theorem coe_cuspVerticalPoint (x y : ℝ) (hy : 0 < y) :
    (cuspVerticalPoint x y hy : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I := rfl

/-- Positivity of the height at the dual rational cusp. -/
theorem dualCuspHeight_pos (q y : ℝ) (hq : q ≠ 0) (hy : 0 < y) :
    0 < 1 / (q ^ 2 * y) := by positivity

/-- The elementary geometry of the rational-cusp change of variables. -/
theorem cusp_matrix_action (γ : SL(2, ℤ)) (y : ℝ)
    (hq : γ 1 0 ≠ 0) (hy : 0 < y) :
    γ • cuspVerticalPoint (-(γ 1 1 : ℝ) / γ 1 0)
      (1 / ((γ 1 0 : ℝ) ^ 2 * y))
      (dualCuspHeight_pos _ _ (by exact_mod_cast hq) hy) =
        cuspVerticalPoint ((γ 0 0 : ℝ) / γ 1 0) y hy := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp only [coe_cuspVerticalPoint, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_one,
    algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast]
  have hqC : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hq
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - (γ 0 1 : ℂ) * γ 1 0 = 1 := by
    exact_mod_cast (show γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 by
      simpa only [Matrix.det_fin_two] using γ.det_coe)
  have hd : (γ 1 0 : ℂ) *
      (-(γ 1 1 : ℂ) / γ 1 0 + 1 / ((γ 1 0 : ℂ) ^ 2 * y) * Complex.I) + γ 1 1 =
        Complex.I / ((γ 1 0 : ℂ) * y) := by
    field_simp
    ring
  rw [hd]
  field_simp [hqC, hyC, Complex.I_ne_zero]
  linear_combination -(γ 1 0 : ℂ) * y * hdet - (γ 1 0 : ℂ) * y * Complex.I_sq

/-- The automorphy factor at the dual cusp, including its exact reciprocal. -/
theorem cusp_matrix_denom (γ : SL(2, ℤ)) (y : ℝ)
    (hq : γ 1 0 ≠ 0) (hy : 0 < y) :
    denom γ (cuspVerticalPoint (-(γ 1 1 : ℝ) / γ 1 0)
      (1 / ((γ 1 0 : ℝ) ^ 2 * y))
      (dualCuspHeight_pos _ _ (by exact_mod_cast hq) hy)) =
        Complex.I / ((γ 1 0 : ℂ) * y) := by
  rw [ModularGroup.denom_apply]
  simp only [coe_cuspVerticalPoint, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_intCast]
  have hqC : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hq
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp
  ring

/-- Equation (5.2) without a character: it follows from weight-one modularity
whenever the cusp matrix belongs to the actual invariance group. -/
theorem weightOne_cusp_transform {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup SL(2, ℤ)} [SlashInvariantFormClass F Γ 1]
    (f : F) (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (y : ℝ)
    (hq : γ 1 0 ≠ 0) (hy : 0 < y) :
    f (cuspVerticalPoint ((γ 0 0 : ℝ) / γ 1 0) y hy) =
      (Complex.I / ((γ 1 0 : ℂ) * y)) *
        f (cuspVerticalPoint (-(γ 1 1 : ℝ) / γ 1 0)
          (1 / ((γ 1 0 : ℝ) ^ 2 * y))
          (dualCuspHeight_pos _ _ (by exact_mod_cast hq) hy)) := by
  rw [← cusp_matrix_action γ y hq hy]
  rw [SlashInvariantForm.slash_action_eqn_SL'' f hγ, zpow_one,
    cusp_matrix_denom γ y hq hy]

/-- The negative-matrix variant supplies the negative quadratic-character
branch while retaining a genuine group-membership hypothesis. -/
theorem weightOne_cusp_transform_neg {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup SL(2, ℤ)} [SlashInvariantFormClass F Γ 1]
    (f : F) (γ : SL(2, ℤ)) (hγ : -γ ∈ Γ) (y : ℝ)
    (hq : γ 1 0 ≠ 0) (hy : 0 < y) :
    f (cuspVerticalPoint ((γ 0 0 : ℝ) / γ 1 0) y hy) =
      -(Complex.I / ((γ 1 0 : ℂ) * y)) *
        f (cuspVerticalPoint (-(γ 1 1 : ℝ) / γ 1 0)
          (1 / ((γ 1 0 : ℝ) ^ 2 * y))
          (dualCuspHeight_pos _ _ (by exact_mod_cast hq) hy)) := by
  rw [← cusp_matrix_action γ y hq hy, ← ModularGroup.SL_neg_smul γ]
  rw [SlashInvariantForm.slash_action_eqn_SL'' f hγ, zpow_one]
  have hden : ∀ z : ℍ, denom (-γ : SL(2, ℤ)) z = -denom γ z := by
    intro z
    simp only [ModularGroup.denom_apply]
    simp
    ring
  rw [hden, cusp_matrix_denom γ y hq hy]

/-- Exponential-test summation at a rational cusp, derived from the actual
q-expansion and weight-one modularity. This is not the general Bessel-test
Voronoi formula. Both infinite sums converge by `ModularForm.hasSum_qExpansion`. -/
theorem weightOne_qExpansion_cusp_transform {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup SL(2, ℤ)} [ModularFormClass F Γ 1]
    [Fact (IsCusp .infty (Γ : Subgroup (GL (Fin 2) ℝ)))]
    (f : F) (hperiod : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (y : ℝ)
    (hq : γ 1 0 ≠ 0) (hy : 0 < y) :
    (∑' n : ℕ, (qExpansion 1 f).coeff n *
      Function.Periodic.qParam 1 (cuspVerticalPoint ((γ 0 0 : ℝ) / γ 1 0) y hy) ^ n) =
      (Complex.I / ((γ 1 0 : ℂ) * y)) *
        ∑' n : ℕ, (qExpansion 1 f).coeff n *
          Function.Periodic.qParam 1 (cuspVerticalPoint (-(γ 1 1 : ℝ) / γ 1 0)
            (1 / ((γ 1 0 : ℝ) ^ 2 * y))
            (dualCuspHeight_pos _ _ (by exact_mod_cast hq) hy)) ^ n := by
  rw [(ModularForm.hasSum_qExpansion f (by norm_num) hperiod _).tsum_eq,
    (ModularForm.hasSum_qExpansion f (by norm_num) hperiod _).tsum_eq]
  exact weightOne_cusp_transform f γ hγ y hq hy

end ArtinMatthews
