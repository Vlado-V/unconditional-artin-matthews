module

public import ArtinMatthews.SpectralGamma0EllipticCoordinates
public import ArtinMatthews.SpectralRellichGreenEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Actual scalar Euclidean H¹ energy of the real/imaginary projection of a
compact localized complex section, with the exact coordinate Jacobian. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff SchwartzMap LineDeriv

namespace ArtinMatthews

def spectralEllipticScalarEnergy (L : ℂ →L[ℝ] ℝ) (F : SchwartzMap (ℝ × ℝ) ℂ) : ℝ :=
  (∫ x : Fin 2 → ℝ, ‖spectralEllipticScalar L F x‖^2) +
    ∫ x : Fin 2 → ℝ, ∑ i : Fin 2,
      ‖fderiv ℝ (spectralEllipticScalar L F) x (Pi.single i 1)‖^2

theorem spectralPlaneDirection_energy (F : SchwartzMap (ℝ × ℝ) ℂ) (p : ℝ × ℝ) :
    (∑ i : Fin 2, ‖fderiv ℝ F p (spectralPlaneDirection i)‖^2) =
      h2DirichletDensity F F p := by
  simp only [Fin.sum_univ_two,spectralPlaneDirection,Matrix.cons_val_zero,
    Matrix.cons_val_one,h2DirichletDensity,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,real_inner_self_eq_norm_sq]

theorem spectralEllipticScalarEnergy_le (L : ℂ →L[ℝ] ℝ)
    (F : SchwartzMap (ℝ × ℝ) ℂ) (hc : HasCompactSupport F) :
    spectralEllipticScalarEnergy L F ≤
      ‖L‖^2 * ((∫ p, ‖F p‖^2) + ∫ p, h2DirichletDensity F F p) := by
  have hu := spectralEllipticScalar_contDiff L F (F.smooth (⊤ : ℕ∞))
  have hs := spectralEllipticScalar_compact L F hc
  have hi : Integrable (fun x : Fin 2 → ℝ => ‖spectralEllipticScalar L F x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hu.continuous.aestronglyMeasurable).mp
      (hu.continuous.memLp_of_hasCompactSupport hs)
  have hdi (i : Fin 2) : Integrable (fun x : Fin 2 → ℝ =>
      ‖fderiv ℝ (spectralEllipticScalar L F) x (Pi.single i 1)‖^2) := by
    have hcont := (hu.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := Pi.single i 1))
    exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mp
      (hcont.memLp_of_hasCompactSupport (hs.fderiv_apply (𝕜 := ℝ) _))
  have hFi : Integrable (fun p : ℝ × ℝ => ‖F p‖^2) :=
    (memLp_two_iff_integrable_sq_norm F.continuous.aestronglyMeasurable).mp (F.continuous.memLp_of_hasCompactSupport hc)
  have hFc := (spectralEllipticCoordinates_measurePreserving.integrable_comp
    (g := fun p : ℝ × ℝ => ‖F p‖^2) hFi.aestronglyMeasurable).mpr hFi
  have hDc := (spectralEllipticCoordinates_measurePreserving.integrable_comp
    (g := fun p : ℝ × ℝ => h2DirichletDensity F F p)
    (h2DirichletDensity_integrable F F).aestronglyMeasurable).mpr (h2DirichletDensity_integrable F F)
  have hval : (∫ x : Fin 2 → ℝ, ‖spectralEllipticScalar L F x‖^2) ≤
      ‖L‖^2 * ∫ p, ‖F p‖^2 := by
    calc
      _ ≤ ∫ x : Fin 2 → ℝ, ‖L‖^2 * ‖F (spectralEllipticCoordinates x)‖^2 :=
        integral_mono hi (hFc.const_mul _) (spectralEllipticScalar_sq_le L F)
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        exact spectralEllipticCoordinates_integral (fun p => ‖F p‖^2)
  have hgrad : (∫ x : Fin 2 → ℝ, ∑ i : Fin 2,
      ‖fderiv ℝ (spectralEllipticScalar L F) x (Pi.single i 1)‖^2) ≤
      ‖L‖^2 * ∫ p, h2DirichletDensity F F p := by
    calc
      _ ≤ ∫ x : Fin 2 → ℝ, ‖L‖^2 * h2DirichletDensity F F (spectralEllipticCoordinates x) := by
        apply integral_mono (integrable_finsetSum _ (fun i _ => hdi i)) (hDc.const_mul _)
        intro x
        change (∑ i : Fin 2, ‖fderiv ℝ (spectralEllipticScalar L F) x (Pi.single i 1)‖^2) ≤
          ‖L‖^2 * h2DirichletDensity F F (spectralEllipticCoordinates x)
        simpa only [spectralPlaneDirection_energy] using
          spectralEllipticScalar_derivative_sq_le L F (F.smooth (⊤ : ℕ∞)) x
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        exact spectralEllipticCoordinates_integral (h2DirichletDensity F F)
  exact (add_le_add hval hgrad).trans_eq (mul_add _ _ _).symm

end ArtinMatthews
