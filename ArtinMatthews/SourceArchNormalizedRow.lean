module

public import ArtinMatthews.SourceKPArchTranslatedDerivativeBound


set_option backward.privateInPublic true
@[expose] public section

/-! Separate the scale of a complex bottom row from its contribution to the
spatial variation of the spherical profile. -/

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups ContDiff
noncomputable section

def sourceArchNormalizedRow (u : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ‖u‖⁻¹ • u

theorem sourceArchNormalizedRow_norm (u : Fin 2 → ℂ) (hu : u ≠ 0) :
    ‖sourceArchNormalizedRow u‖ = 1 := by
  rw [sourceArchNormalizedRow, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]

def sourceArchRowCoordinateProfile (s : ℂ) (up : (Fin 2 → ℂ) × EuclideanSpatial) : ℂ :=
  Complex.exp ((2 * s + 1) * (rowLogHeight up.1 up.2.ofLp : ℂ))

theorem sourceArchRowCoordinateProfile_ne_zero (s : ℂ) (up : (Fin 2 → ℂ) × EuclideanSpatial) :
    sourceArchRowCoordinateProfile s up ≠ 0 :=
  Complex.exp_ne_zero _

private theorem heightDenominator_real_smul (z : ℂ) (y r : ℝ) (u : Fin 2 → ℂ) :
    heightDenominator z y (r • u) = r ^ 2 * heightDenominator z y u := by
  have h : (r • u) 0 * z + (r • u) 1 = r • (u 0 * z + u 1) := by
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  rw [heightDenominator, h, Pi.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, heightDenominator]
  ring

private theorem rowLogHeight_real_smul (u : Fin 2 → ℂ) (hu : u ≠ 0)
    (p : SpatialCoordinates) (hp : 0 < p 2) (r : ℝ) (hr : 0 < r) :
    rowLogHeight (r • u) p = rowLogHeight u p - 2 * Real.log r := by
  let z := (p 0 : ℂ) + (p 1 : ℂ) * Complex.I
  have hpos := heightDenominator_pos z (p 2) hp u hu
  simp only [rowLogHeight, ← heightDenominator_eq_quadratic]
  change Real.log (p 2) - Real.log (heightDenominator z (p 2) (r • u)) =
    Real.log (p 2) - Real.log (heightDenominator z (p 2) u) - 2 * Real.log r
  rw [heightDenominator_real_smul, Real.log_mul (pow_ne_zero _ hr.ne') hpos.ne',
    Real.log_pow]
  ring

theorem sourceArchRowCoordinateProfile_contDiffAt (s : ℂ) (u : Fin 2 → ℂ)
    (p : EuclideanSpatial) (hu : u ≠ 0) (hp : 0 < p 2) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceArchRowCoordinateProfile s) (u, p) := by
  let D := fun up : (Fin 2 → ℂ) × EuclideanSpatial =>
    quadraticHeightDenominator (Complex.normSq (up.1 0))
      ((up.1 0 * star (up.1 1)).re) (-(up.1 0 * star (up.1 1)).im)
      (Complex.normSq (up.1 1)) (up.2 0) (up.2 1) (up.2 2)
  have hD : ContDiff ℝ (∞ : ℕ∞ω) D := by
    simp only [D, quadraticHeightDenominator, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    simp only [← Complex.reCLM_apply, ← Complex.imCLM_apply]
    fun_prop
  have hDpos : 0 < D (u, p) := by
    simpa only [D, heightDenominator_eq_quadratic] using
      heightDenominator_pos ((p 0 : ℂ) + (p 1 : ℂ) * Complex.I) (p 2) hp u hu
  have hy : ContDiffAt ℝ (∞ : ℕ∞ω)
      (fun up : (Fin 2 → ℂ) × EuclideanSpatial => up.2 2) (u, p) := by fun_prop
  have hlog := (hy.log hp.ne').sub (hD.contDiffAt.log hDpos.ne')
  unfold sourceArchRowCoordinateProfile
  exact (contDiffAt_const.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp (u, p) hlog)).cexp

def sourceArchTranslatedRowScale (s : ℂ) (g : GL (Fin 2) ℂ) : ℂ :=
  (‖(GeneralLinearGroup.det g : ℂ)‖ : ℂ) ^ (2 * s + 1) *
    Complex.exp ((2 * s + 1) * ((-2 * Real.log ‖sourceArchTranslatedRow g‖ : ℝ) : ℂ))

theorem sourceArchTranslatedProfile_eq_normalizedRow (s : ℂ) (g : GL (Fin 2) ℂ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceArchTranslatedProfile s g p =
      sourceArchTranslatedRowScale s g *
        sourceArchRowCoordinateProfile s (sourceArchNormalizedRow (sourceArchTranslatedRow g), p) := by
  let u := sourceArchTranslatedRow g
  have hu : u ≠ 0 := sourceArchTranslatedRow_ne_zero g
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have h := rowLogHeight_real_smul u hu p.ofLp hp ‖u‖⁻¹ (inv_pos.mpr hr)
  have hlog : rowLogHeight u p.ofLp =
      -2 * Real.log ‖u‖ + rowLogHeight (sourceArchNormalizedRow u) p.ofLp := by
    rw [sourceArchNormalizedRow, h, Real.log_inv]
    ring
  calc
    sourceArchTranslatedProfile s g p =
        (‖(GeneralLinearGroup.det g : ℂ)‖ : ℂ) ^ (2 * s + 1) *
          Complex.exp ((2 * s + 1) * (rowLogHeight u p.ofLp : ℂ)) := by
      simpa only [WithLp.toLp_ofLp] using sourceArchTranslatedProfile_eq_exp s g p.ofLp
    _ = _ := by
      unfold sourceArchTranslatedRowScale sourceArchRowCoordinateProfile
      rw [hlog, Complex.ofReal_add, mul_add, Complex.exp_add]
      simp only [u]
      ring

end
end ArtinMatthews.SourceArchJacquet
