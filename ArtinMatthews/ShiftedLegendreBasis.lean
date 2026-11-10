module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import ArtinMatthews.ShiftedLegendreIntervalLp
public import ArtinMatthews.ShiftedLegendreDense
public import ArtinMatthews.ShiftedLegendreOrthogonality
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized shifted Legendre Hilbert basis and interval expansions. -/
namespace ArtinMatthews
open MeasureTheory Set
open scoped unitInterval
noncomputable section

def shiftedLegendreScale (n : ℕ) : ℝ := Real.sqrt (2 * (n : ℝ) + 1)

theorem shiftedLegendreScale_pos (n : ℕ) : 0 < shiftedLegendreScale n :=
  Real.sqrt_pos.2 (by positivity)

theorem shiftedLegendreScale_sq (n : ℕ) : shiftedLegendreScale n ^ 2 = 2 * (n : ℝ) + 1 :=
  Real.sq_sqrt (by positivity)

theorem shiftedLegendreScale_mul (n : ℕ) :
    (shiftedLegendreScale n : ℂ) * (shiftedLegendreScale n : ℂ) =
      ((2 * (n : ℝ) + 1 : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← pow_two, shiftedLegendreScale_sq]

def shiftedLegendreNormalized (n : ℕ) : ShiftedLegendreL2 :=
  (shiftedLegendreScale n : ℂ) • shiftedLegendreVector n

theorem shiftedLegendreNormalized_orthonormal : Orthonormal ℂ shiftedLegendreNormalized := by
  constructor
  · intro n
    have hsq : ‖shiftedLegendreNormalized n‖ ^ 2 = 1 := by
      rw [shiftedLegendreNormalized, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (shiftedLegendreScale_pos n), shiftedLegendreScale_sq,
        shiftedLegendreVector_norm_sq]
      exact mul_inv_cancel₀ (by positivity)
    nlinarith [norm_nonneg (shiftedLegendreNormalized n)]
  · intro i j hij
    simp only [shiftedLegendreNormalized, inner_smul_left, inner_smul_right,
      shiftedLegendreVector_inner, ite_eq_right hij, mul_zero]

theorem shiftedLegendreNormalized_dense_span :
    (Submodule.span ℂ (range shiftedLegendreNormalized)).topologicalClosure = ⊤ := by
  have hspan : Submodule.span ℂ (range shiftedLegendreNormalized) =
      Submodule.span ℂ (range shiftedLegendreVector) := by
    apply le_antisymm <;> apply Submodule.span_le.mpr
    · rintro _ ⟨n, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self n))
    · rintro _ ⟨n, rfl⟩
      have hn : (shiftedLegendreScale n : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (shiftedLegendreScale_pos n).ne'
      have h := (Submodule.span ℂ (range shiftedLegendreNormalized)).smul_mem
        (shiftedLegendreScale n : ℂ)⁻¹ (Submodule.subset_span (mem_range_self n))
      change shiftedLegendreVector n ∈ Submodule.span ℂ (range shiftedLegendreNormalized)
      simpa only [shiftedLegendreNormalized, smul_smul, inv_mul_cancel₀ hn, one_smul] using h
  rw [hspan, shiftedLegendreVector_dense_span]

def shiftedLegendreBasis : HilbertBasis ℕ ℂ ShiftedLegendreL2 :=
  HilbertBasis.mk shiftedLegendreNormalized_orthonormal shiftedLegendreNormalized_dense_span.ge

@[simp] theorem shiftedLegendreBasis_apply (n : ℕ) :
    shiftedLegendreBasis n = shiftedLegendreNormalized n :=
  congrFun (HilbertBasis.coe_mk _ _) n

theorem shiftedLegendreBasis_inner_toLp (n : ℕ) {f : ℝ → ℂ} (hf : ContinuousOn f I) :
    inner ℂ (shiftedLegendreBasis n) (shiftedLegendreToLp (shiftedLegendreRestrict f hf)) =
      (shiftedLegendreScale n : ℂ) *
        ∫ x in (0 : ℝ)..1, (shiftedLegendreValue n x : ℂ) * f x := by
  rw [shiftedLegendreBasis_apply, shiftedLegendreNormalized, inner_smul_left,
    Complex.conj_ofReal, shiftedLegendreVector_inner_toLp]

theorem shiftedLegendreBasis_hasSum (f : ShiftedLegendreL2) :
    HasSum (fun n => inner ℂ (shiftedLegendreBasis n) f • shiftedLegendreBasis n) f := by
  simpa only [HilbertBasis.repr_apply_apply] using shiftedLegendreBasis.hasSum_repr f

theorem shiftedLegendreToLp_hasSum {f : ℝ → ℂ} (hf : ContinuousOn f I) :
    HasSum (fun n : ℕ => (((2 * (n : ℝ) + 1 : ℝ) : ℂ) *
        ∫ x in (0 : ℝ)..1, (shiftedLegendreValue n x : ℂ) * f x) • shiftedLegendreVector n)
      (shiftedLegendreToLp (shiftedLegendreRestrict f hf)) := by
  refine HasSum.congr_fun (shiftedLegendreBasis_hasSum _) (fun n => ?_)
  rw [shiftedLegendreBasis_inner_toLp, shiftedLegendreBasis_apply, shiftedLegendreNormalized,
    smul_smul, ← shiftedLegendreScale_mul n]
  congr 1
  ring

theorem shiftedLegendreBasis_parseval (f g : ShiftedLegendreL2) :
    HasSum (fun n => inner ℂ f (shiftedLegendreBasis n) * inner ℂ (shiftedLegendreBasis n) g)
      (inner ℂ f g) :=
  shiftedLegendreBasis.hasSum_inner_mul_inner f g

theorem shiftedLegendreInterval_bilinear_hasSum {f g : ℝ → ℂ}
    (hf : ContinuousOn f I) (hg : ContinuousOn g I) :
    HasSum (fun n : ℕ => ((2 * (n : ℝ) + 1 : ℝ) : ℂ) *
      (∫ x in (0 : ℝ)..1, (shiftedLegendreValue n x : ℂ) * f x) *
      (∫ x in (0 : ℝ)..1, (shiftedLegendreValue n x : ℂ) * g x))
      (∫ x in (0 : ℝ)..1, f x * g x) := by
  let F := shiftedLegendreToLp (shiftedLegendreRestrict (fun x => star (f x)) hf.star)
  let G := shiftedLegendreToLp (shiftedLegendreRestrict g hg)
  have hfg : inner ℂ F G = ∫ x in (0 : ℝ)..1, f x * g x := by
    dsimp only [F, G]
    rw [shiftedLegendreToLp_inner_interval]
    simp only [star_star]
  have hleft (n : ℕ) : inner ℂ F (shiftedLegendreBasis n) =
      (shiftedLegendreScale n : ℂ) *
        ∫ x in (0 : ℝ)..1, (shiftedLegendreValue n x : ℂ) * f x := by
    rw [shiftedLegendreBasis_apply, shiftedLegendreNormalized, inner_smul_right]
    dsimp only [F, shiftedLegendreVector, shiftedLegendreContinuous]
    rw [shiftedLegendreToLp_inner_interval]
    simp only [star_star, mul_comm (f _)]
  have h := shiftedLegendreBasis_parseval F G
  rw [hfg] at h
  refine HasSum.congr_fun h (fun n => ?_)
  change _ = inner ℂ F (shiftedLegendreBasis n) *
    inner ℂ (shiftedLegendreBasis n) (shiftedLegendreToLp (shiftedLegendreRestrict g hg))
  rw [hleft, shiftedLegendreBasis_inner_toLp, ← shiftedLegendreScale_mul n]
  ring

end
end ArtinMatthews
