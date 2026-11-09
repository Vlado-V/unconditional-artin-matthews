module

public import ArtinMatthews.SourceCircleHaar
public import ArtinMatthews.SourceComplexMellinWeightedSup


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set
open ArtinMatthews.VaryingKummerAnalytic
open scoped SchwartzMap ENNReal
noncomputable section

variable {Y : Type*}

def sourceSheetComplexCoordinate (N : Y → ℝ) (t : ℝ) (θ : Circle) (y : Y) : ℂ :=
  (Real.exp ((t - Real.log (N y)) / 2) : ℂ) * θ

theorem sourceSheetComplexCoordinate_norm (N : Y → ℝ) (t : ℝ) (θ : Circle) (y : Y) :
    ‖sourceSheetComplexCoordinate N t θ y‖ = Real.exp ((t - Real.log (N y)) / 2) := by
  rw [sourceSheetComplexCoordinate, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Circle.norm_coe, mul_one]

theorem sourceSheetComplexCoordinate_norm_pow (N : Y → ℝ) (hN : ∀ y, 0 < N y)
    (σ t : ℝ) (θ : Circle) (y : Y) :
    (‖sourceSheetComplexCoordinate N t θ y‖ ^ 2) ^ σ * (N y) ^ σ = Real.exp (σ * t) := by
  rw [sourceSheetComplexCoordinate_norm, Real.rpow_def_of_pos (pow_pos (Real.exp_pos _) _) σ,
    Real.rpow_def_of_pos (hN y) σ, ← Real.exp_add, Real.log_pow, Real.log_exp]
  congr 1
  push_cast
  ring

/-- All remaining coordinates keep their exact normalized norm weights. -/
theorem sourceSheetComplexCoordinate_weighted_sup (N : Y → ℝ) (hN : ∀ y, 0 < N y)
    (g : 𝓢(ℂ, ℂ)) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (θ : Circle) (y : Y),
      ‖g (sourceSheetComplexCoordinate N t θ y)‖ ≤
        (C * Real.exp (-σ * t)) * (N y) ^ σ := by
  obtain ⟨C, hC, hC'⟩ := sourceComplexSchwartz_weighted_dilate_sup g σ hσ
  refine ⟨C, hC, ?_⟩
  intro t θ y
  let z := sourceSheetComplexCoordinate N t θ y
  have hz : ‖g z‖ * (‖z‖ ^ 2) ^ σ ≤ C := by
    simpa only [Real.exp_zero, one_smul] using hC' 0 (by norm_num) z
  have hpow := sourceSheetComplexCoordinate_norm_pow N hN σ t θ y
  have hb := mul_le_mul_of_nonneg_right hz (Real.rpow_nonneg (hN y).le σ)
  rw [mul_assoc, hpow] at hb
  calc
    ‖g z‖ ≤ C * (N y) ^ σ / Real.exp (σ * t) :=
      (le_div_iff₀ (Real.exp_pos (σ * t))).mpr hb
    _ = _ := by rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul]; ring

end
end ArtinMatthews.SourcePhysical
