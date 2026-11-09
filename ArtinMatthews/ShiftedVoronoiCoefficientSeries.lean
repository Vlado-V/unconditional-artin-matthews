module

public import ArtinMatthews.ShiftedBilinear
public import ArtinMatthews.ShiftedVoronoiReflection
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet


set_option backward.privateInPublic true
@[expose] public section

/-!
# Absolute convergence for additive twists of a weight-one cusp form

The coefficients are those of the actual period-one q-expansion. Their absolute
Dirichlet series converges on `re s > 1`, using the proved mean-square bound.
-/

noncomputable section
open Complex UpperHalfPlane Finset Filter Asymptotics
open scoped Topology

namespace ArtinMatthews

/-- The additive twist of the actual period-one Fourier coefficients. -/
def cuspAdditiveCoeff {F : Type*} [FunLike F ℍ ℂ] (f : F) (x : ℝ) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n * Complex.exp (2 * Real.pi * Complex.I * n * x)

@[simp] theorem norm_cuspAdditiveCoeff {F : Type*} [FunLike F ℍ ℂ]
    (f : F) (x : ℝ) (n : ℕ) :
    ‖cuspAdditiveCoeff f x n‖ = ‖(qExpansion 1 f).coeff n‖ := by
  simp [cuspAdditiveCoeff, Complex.norm_exp]

/-- The zero coefficient vanishes by cuspidality, including after an additive twist. -/
@[simp] theorem cuspAdditiveCoeff_zero
    {Γ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) (x : ℝ) :
    cuspAdditiveCoeff f x 0 = 0 := by
  simp [cuspAdditiveCoeff, CuspFormClass.qExpansion_coeff_zero f (by norm_num) hperiod]

/-- The absolute partial sums are `O(N)`, not merely `O(N^(3/2))` from a
pointwise coefficient estimate. The bound is uniform in the additive twist. -/
theorem weightOne_sum_norm_additiveCoeff_le
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (T : ℕ),
      ∑ n ∈ Finset.range T, ‖cuspAdditiveCoeff f x n‖ ≤ C * T := by
  obtain ⟨C, hC, hbound⟩ := weightOne_sum_norm_sq_le f hperiod
    (fun n ↦ (qExpansion 1 f).coeff n) (fun _ ↦ rfl)
  refine ⟨C + 1, by positivity, fun x T ↦ ?_⟩
  simp only [norm_cuspAdditiveCoeff]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range T)
    (fun _ ↦ (1 : ℝ)) (fun n ↦ ‖(qExpansion 1 f).coeff n‖)
  simp only [one_mul, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at hcs
  have hb := mul_le_mul_of_nonneg_left (hbound T) (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
  have hn : 0 ≤ ∑ n ∈ Finset.range T, ‖(qExpansion 1 f).coeff n‖ :=
    Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  apply (sq_le_sq₀ hn (mul_nonneg (by positivity) hT)).mp
  have hC2 : C ≤ (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
  calc
    _ ≤ C * (T : ℝ) ^ 2 := by nlinarith [hcs, hb]
    _ ≤ (C + 1) ^ 2 * (T : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hC2 (sq_nonneg _)
    _ = _ := by ring

/-- Absolute convergence of every additive twist in the full half-plane
`re s > 1`, derived from the actual cusp-form mean square. -/
theorem weightOne_additiveCoeff_LSeriesSummable
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (x : ℝ) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (cuspAdditiveCoeff f x) s := by
  obtain ⟨C, hC, hbound⟩ := weightOne_sum_norm_additiveCoeff_le f hperiod
  apply LSeriesSummable_of_sum_norm_bigO (r := 1) ?_ (by norm_num) hs
  refine IsBigO.of_bound (2 * C) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
  simp only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  calc
    ∑ n ∈ Icc 1 N, ‖cuspAdditiveCoeff f x n‖ ≤
        ∑ n ∈ range (N + 1), ‖cuspAdditiveCoeff f x n‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
      · intro n _ _
        exact norm_nonneg _
    _ ≤ C * (N + 1) := by exact_mod_cast hbound x (N + 1)
    _ ≤ 2 * C * N := by
      have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith

end ArtinMatthews
