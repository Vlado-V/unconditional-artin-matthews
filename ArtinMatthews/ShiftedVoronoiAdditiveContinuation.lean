module

public import ArtinMatthews.ShiftedVoronoiCoefficientMellin


set_option backward.privateInPublic true
@[expose] public section

/-!
# Entire continuation and left-half-plane equation of an additive twist

These statements concern the actual q-expansion coefficients. The continuation
is defined from the convergent cusp Mellin integral, and agreement with the
Dirichlet series is proved. The reflected right-half-plane series is obtained
from genuine modularity, rather than supplied as a functional-equation input.
-/

noncomputable section
open Complex UpperHalfPlane MeasureTheory Set
open scoped MatrixGroups

namespace ArtinMatthews

/-- The continuation naturally normalized to equal the coefficient L-series. -/
def cuspAdditiveL {F : Type*} [FunLike F ℍ ℂ] (f : F) (x : ℝ) (s : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) ^ s * (Complex.Gamma s)⁻¹ *
    mellin (cuspVerticalRestriction f x) s

/-- The continuation is entire at every rational additive twist. -/
theorem cuspAdditiveL_differentiable
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (x : ℚ) :
    Differentiable ℂ (cuspAdditiveL f (x : ℝ)) := by
  unfold cuspAdditiveL
  have hp : Differentiable ℂ (fun s : ℂ ↦ ((2 * Real.pi : ℝ) : ℂ) ^ s) :=
    differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  exact (hp.mul Complex.differentiable_one_div_Gamma).mul
    (cuspVerticalRestriction_mellin_differentiable (by norm_num) f x)

/-- Agreement with the absolutely convergent coefficient Dirichlet series. -/
theorem cuspAdditiveL_eq_LSeries
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (x : ℝ) (s : ℂ) (hs : 1 < s.re) :
    cuspAdditiveL f x s = LSeries (cuspAdditiveCoeff f x) s := by
  rw [cuspAdditiveL, weightOne_additiveCoeff_mellin f hperiod x s hs,
    Complex.cpow_neg]
  have hg : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hp : ((2 * Real.pi : ℝ) : ℂ) ^ s ≠ 0 :=
    (Complex.cpow_ne_zero_iff).mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  field_simp

/-- On the left half-plane, modularity expresses the entire continuation in
terms of the absolutely convergent series at the dual rational cusp. -/
theorem cuspAdditiveL_reflected_series
    {Γ : Subgroup SL(2, ℤ)} [(Γ : Subgroup (GL (Fin 2) ℝ)).IsArithmetic]
    (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (hq : γ 1 0 ≠ 0)
    (s : ℂ) (hs : s.re < 0) :
    cuspAdditiveL f ((γ 0 0 : ℝ) / γ 1 0) s =
      (((2 * Real.pi : ℝ) : ℂ) ^ s * (Complex.Gamma s)⁻¹) *
        ((Complex.I / (γ 1 0 : ℂ)) * (((γ 1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (1 - s)) *
        (((2 * Real.pi : ℝ) : ℂ) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
          LSeries (cuspAdditiveCoeff f (-(γ 1 1 : ℝ) / γ 1 0)) (1 - s)) := by
  rw [cuspAdditiveL, weightOne_vertical_mellin_reflection f γ hγ hq s,
    weightOne_additiveCoeff_mellin f hperiod _ (1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)]
  ring

/-- Endpoint convergence bounds a Mellin transform uniformly throughout the
closed vertical strip between the two endpoints. -/
theorem mellin_norm_le_on_strip (f : ℝ → ℂ) (a b : ℝ)
    (ha : MellinConvergent f (a : ℂ)) (hb : MellinConvergent f (b : ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖mellin f s‖ ≤ C := by
  let B : ℝ → ℝ := fun y ↦ ‖(y : ℂ) ^ ((a : ℂ) - 1) * f y‖ +
    ‖(y : ℂ) ^ ((b : ℂ) - 1) * f y‖
  have hB : IntegrableOn B (Ioi 0) := ha.norm.add hb.norm
  refine ⟨∫ y in Ioi 0, B y, integral_nonneg (fun _ ↦ by dsimp [B]; positivity), ?_⟩
  intro s hsa hsb
  unfold mellin
  apply norm_integral_le_of_norm_le hB
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hp : y ^ (s.re - 1) ≤ y ^ (a - 1) + y ^ (b - 1) := by
    by_cases h1 : 1 ≤ y
    · exact (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hy.le _))
    · exact (Real.rpow_le_rpow_of_exponent_ge hy (le_of_not_ge h1) (by linarith)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hy.le _))
  change ‖(y : ℂ) ^ (s - 1) * f y‖ ≤ B y
  dsimp only [B]
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.sub_re,
    Complex.ofReal_re, Complex.one_re]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (f y))

/-- The completed additive twist has a uniform bound on every closed strip,
with all endpoint convergence hypotheses discharged by cuspidality. -/
theorem cuspVerticalRestriction_mellin_strip_bound
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (x : ℚ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖mellin (cuspVerticalRestriction f (x : ℝ)) s‖ ≤ C :=
  mellin_norm_le_on_strip _ a b
    (cuspVerticalRestriction_mellinConvergent (by norm_num) f x a)
    (cuspVerticalRestriction_mellinConvergent (by norm_num) f x b)

end ArtinMatthews
