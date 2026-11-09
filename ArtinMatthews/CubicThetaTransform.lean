module

public import OAI.NumberTheory.DirichletL.Poisson.BinaryGaussian
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!+# Complex Eisenstein Gaussian inversion

The analytic Gaussian identities here are proved from Poisson summation. They
do not assert modularity or cuspidality of a character-weighted theta series.
-/

noncomputable section
open scoped BigOperators
open Complex UpperHalfPlane
open OAI

namespace ArtinMatthews

/-- The complex Gaussian associated to the Eisenstein norm form. -/
def eisensteinComplexGaussian (a : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * a *
    ((z.1 : ℂ) ^ 2 - (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2))

theorem eisensteinComplexGaussian_summable {a : ℂ} (ha : 0 < a.re) :
    Summable (eisensteinComplexGaussian a) := by
  have h := RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (fun z : ℤ × ℤ => a *
      ((z.1 : ℂ) ^ 2 - (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2))
    (eps := a.re / 2) (by positivity) ?_
  · convert h using 1
    ext z
    unfold eisensteinComplexGaussian
    congr 1
    ring
  intro z
  simp [mul_re, mul_im, pow_two]
  nlinarith [mul_nonneg ha.le (sq_nonneg ((z.1 : ℝ) - (z.2 : ℝ)))]

theorem eisenstein_schur {a : ℂ} (ha : a ≠ 0) :
    RankTwoComplex.schur a (-a / 2) a = 3 * a / 4 := by
  unfold RankTwoComplex.schur
  field_simp
  ring

theorem eisenstein_schur_re {a : ℂ} (ha : 0 < a.re) :
    0 < (RankTwoComplex.schur a (-a / 2) a).re := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  rw [eisenstein_schur ha0]
  simpa [div_eq_mul_inv, mul_re, mul_im] using (show 0 < 3 * a.re / 4 by positivity)

theorem eisenstein_binaryGaussian (a : ℂ) (z : ℤ × ℤ) :
    RankTwoComplex.binaryGaussian a (-a / 2) a z =
      eisensteinComplexGaussian a z := by
  unfold RankTwoComplex.binaryGaussian eisensteinComplexGaussian
  congr 1
  ring

theorem eisenstein_inv_re_pos {a : ℂ} (ha : 0 < a.re) : 0 < a⁻¹.re := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  rw [Complex.inv_re]
  exact div_pos ha (Complex.normSq_pos.mpr ha0)

theorem eisenstein_firstGaussian_summable {a : ℂ} (ha : 0 < a.re) :
    Summable (RankTwoComplex.firstGaussian a (-a / 2) a) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hi := eisenstein_inv_re_pos ha
  let eps : ℝ := min a⁻¹.re (3 * a.re / 4)
  have heps : 0 < eps := lt_min hi (by positivity)
  have h := RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (fun z : ℤ × ℤ => a⁻¹ * (z.1 : ℂ) ^ 2 +
      (3 * a / 4) * (z.2 : ℂ) ^ 2 + Complex.I * (z.1 : ℂ) * (z.2 : ℂ)) heps ?_
  · convert h using 1
    ext z
    unfold RankTwoComplex.firstGaussian
    rw [eisenstein_schur ha0, ← Complex.exp_add]
    congr 1
    field_simp
    ring
  intro z
  have h1 : eps ≤ a⁻¹.re := min_le_left _ _
  have h2 : eps ≤ 3 * a.re / 4 := min_le_right _ _
  have hr : (a⁻¹ * (z.1 : ℂ) ^ 2 +
      (3 * a / 4) * (z.2 : ℂ) ^ 2 + Complex.I * (z.1 : ℂ) * (z.2 : ℂ)).re =
      a⁻¹.re * (z.1 : ℝ) ^ 2 + (3 * a.re / 4) * (z.2 : ℝ) ^ 2 := by
    simp [mul_re, mul_im, pow_two, div_eq_mul_inv]
  rw [hr]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg (z.1 : ℝ)),
    mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg (z.2 : ℝ))]

theorem eisenstein_dual_parameter_re {a : ℂ} (ha : 0 < a.re) :
    0 < (4 / (3 * a)).re := by
  have hi := eisenstein_inv_re_pos ha
  have heq : 4 / (3 * a) = (4 / 3 : ℂ) * a⁻¹ := by ring
  rw [heq]
  simpa [mul_re] using (show 0 < (4 / 3 : ℝ) * a⁻¹.re by positivity)

theorem eisenstein_dualGaussian {a : ℂ} (ha : a ≠ 0) (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian a (-a / 2) a z =
      eisensteinComplexGaussian (4 / (3 * a)) (z.1, -z.2) := by
  unfold RankTwoComplex.dualGaussian eisensteinComplexGaussian
  rw [eisenstein_schur ha, ← Complex.exp_add]
  push_cast
  congr 1
  field_simp
  ring

theorem eisenstein_dualGaussian_summable {a : ℂ} (ha : 0 < a.re) :
    Summable (RankTwoComplex.dualGaussian a (-a / 2) a) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hs := eisensteinComplexGaussian_summable (eisenstein_dual_parameter_re ha)
  let e : (ℤ × ℤ) ≃ (ℤ × ℤ) := Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hr := e.summable_iff.mpr hs
  convert hr using 1
  ext z
  exact eisenstein_dualGaussian ha0 z

/-- Poisson inversion for the Eisenstein Gaussian, with all convergence
conditions discharged from the positivity of the parameter's real part. -/
theorem eisensteinComplexGaussian_inversion {a : ℂ} (ha : 0 < a.re) :
    (∑' z : ℤ × ℤ, eisensteinComplexGaussian a z) =
      (1 / a ^ (1 / 2 : ℂ)) * (1 / (3 * a / 4) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, eisensteinComplexGaussian (4 / (3 * a)) z := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hO : Summable (RankTwoComplex.binaryGaussian a (-a / 2) a) := by
    convert eisensteinComplexGaussian_summable ha using 1
    ext z
    exact eisenstein_binaryGaussian a z
  have h := RankTwoComplex.binary_gaussian_poisson ha (eisenstein_schur_re ha)
    hO (eisenstein_firstGaussian_summable ha) (eisenstein_dualGaussian_summable ha)
  simp_rw [eisenstein_binaryGaussian, eisenstein_schur ha0, eisenstein_dualGaussian ha0] at h
  rw [h]
  congr 1
  exact (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq
    (eisensteinComplexGaussian (4 / (3 * a)))

/-- The positive-real-part parameter associated to a point of the upper half plane. -/
def eisensteinGaussianParameter (τ : ℍ) : ℂ := -2 * Complex.I * (τ : ℂ)

theorem eisensteinGaussianParameter_re (τ : ℍ) :
    0 < (eisensteinGaussianParameter τ).re := by
  simpa [eisensteinGaussianParameter, mul_re, mul_im] using
    (show 0 < 2 * τ.im from mul_pos (by norm_num) τ.im_pos)

/-- The usual holomorphic Eisenstein lattice theta function. -/
def eisensteinHolomorphicTheta (τ : ℍ) : ℂ :=
  ∑' z : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) *
    ((z.1 : ℂ) ^ 2 - (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2))

theorem eisensteinHolomorphicTheta_summable (τ : ℍ) :
    Summable (fun z : ℤ × ℤ => Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) *
        ((z.1 : ℂ) ^ 2 - (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2))) := by
  convert eisensteinComplexGaussian_summable (eisensteinGaussianParameter_re τ) using 1
  ext z
  unfold eisensteinComplexGaussian eisensteinGaussianParameter
  congr 1
  ring

private theorem positiveReal_mul_cpow {r : ℝ} (hr : 0 < r)
    {a : ℂ} (ha : a ≠ 0) (s : ℂ) :
    ((r : ℂ) * a) ^ s = (r : ℂ) ^ s * a ^ s := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 ha),
    Complex.log_ofReal_mul hr ha, Complex.cpow_def_of_ne_zero hr0,
    Complex.cpow_def_of_ne_zero ha, ← Complex.ofReal_log hr.le, add_mul,
    Complex.exp_add]

theorem eisenstein_inversion_prefactor {a : ℂ} (ha : a ≠ 0) :
    (1 / a ^ (1 / 2 : ℂ)) * (1 / (3 * a / 4) ^ (1 / 2 : ℂ)) =
      2 / ((Real.sqrt 3 : ℂ) * a) := by
  have hp : 3 * a / 4 = ((3 / 4 : ℝ) : ℂ) * a := by push_cast; ring
  have hs : (((3 / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = (Real.sqrt 3 : ℂ) / 2 := by
    have h := Complex.ofReal_cpow (show (0 : ℝ) ≤ 3 / 4 by norm_num) (1 / 2 : ℝ)
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3)] at h
    norm_num at h ⊢
    exact h.symm
  have haa : a ^ (1 / 2 : ℂ) * a ^ (1 / 2 : ℂ) = a := by
    rw [← Complex.cpow_add _ _ ha]
    norm_num
  rw [hp, positiveReal_mul_cpow (by norm_num) ha, hs]
  calc
    _ = 2 / ((Real.sqrt 3 : ℂ) *
        (a ^ (1 / 2 : ℂ) * a ^ (1 / 2 : ℂ))) := by ring
    _ = _ := by rw [haa]

/-- The weight-one prefactor in the Gaussian inversion formula. -/
theorem eisensteinComplexGaussian_inversion_sqrt {a : ℂ} (ha : 0 < a.re) :
    (∑' z : ℤ × ℤ, eisensteinComplexGaussian a z) =
      (2 / ((Real.sqrt 3 : ℂ) * a)) *
        ∑' z : ℤ × ℤ, eisensteinComplexGaussian (4 / (3 * a)) z := by
  rw [eisensteinComplexGaussian_inversion ha,
    eisenstein_inversion_prefactor (by intro h; simp [h] at ha)]

/-- Fricke inversion at the discriminant-three level preserves the upper half plane. -/
def eisensteinFricke (τ : ℍ) : ℍ :=
  ⟨-1 / (3 * (τ : ℂ)), by
    have hτ := τ.im_inv_neg_coe_pos
    have heq : (-1 : ℂ) / (3 * τ) = ((1 / 3 : ℝ) : ℂ) * (-(τ : ℂ))⁻¹ := by
      push_cast
      ring
    rw [heq]
    simpa [mul_im] using (show 0 < (1 / 3 : ℝ) * (-(τ : ℂ))⁻¹.im by positivity)⟩

theorem eisensteinGaussianParameter_fricke (τ : ℍ) :
    eisensteinGaussianParameter (eisensteinFricke τ) =
      4 / (3 * eisensteinGaussianParameter τ) := by
  unfold eisensteinGaussianParameter eisensteinFricke
  field_simp
  simp [Complex.I_sq]
  ring

theorem eisensteinHolomorphicTheta_eq_gaussian (τ : ℍ) :
    eisensteinHolomorphicTheta τ =
      ∑' z : ℤ × ℤ, eisensteinComplexGaussian (eisensteinGaussianParameter τ) z := by
  apply tsum_congr
  intro z
  unfold eisensteinComplexGaussian eisensteinGaussianParameter
  congr 1
  ring

/-- Actual Fricke inversion for the unweighted Eisenstein lattice theta series. -/
theorem eisensteinHolomorphicTheta_fricke (τ : ℍ) :
    eisensteinHolomorphicTheta (eisensteinFricke τ) =
      (-Complex.I * (Real.sqrt 3 : ℂ) * (τ : ℂ)) * eisensteinHolomorphicTheta τ := by
  have h := eisensteinComplexGaussian_inversion_sqrt (eisensteinGaussianParameter_re τ)
  rw [← eisensteinGaussianParameter_fricke, ← eisensteinHolomorphicTheta_eq_gaussian,
    ← eisensteinHolomorphicTheta_eq_gaussian] at h
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)).ne'
  rw [h]
  unfold eisensteinGaussianParameter
  field_simp [τ.ne_zero, hs]

end ArtinMatthews
