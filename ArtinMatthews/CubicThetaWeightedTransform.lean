module

public import ArtinMatthews.CubicThetaTransform
public import ArtinMatthews.CubicTheta
public import ArtinMatthews.CubicThetaHolomorphicLattice
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!+# Periodic weights in complex Eisenstein Gaussian sums

These are analytic Poisson identities for finite periodic weights. Identifying
the transformed weight and proving all cusp conditions for a Hecke character
are separate arithmetic steps.
-/

noncomputable section
open scoped BigOperators
open Complex UpperHalfPlane
open OAI OAI.SevenEighths

namespace ArtinMatthews

/-- The actual periodic weighted lattice Gaussian. -/
def eisensteinWeightedGaussian {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (a : ℂ) : ℂ :=
  ∑' z : ℤ × ℤ, HeckeTheta.periodicCoeff w z * eisensteinComplexGaussian a z

theorem eisensteinWeightedGaussian_summable {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {a : ℂ} (ha : 0 < a.re) :
    Summable (fun z : ℤ × ℤ =>
      HeckeTheta.periodicCoeff w z * eisensteinComplexGaussian a z) := by
  classical
  let C : ℝ := ∑ r, ‖w r‖
  have hbound (z : ℤ × ℤ) : ‖HeckeTheta.periodicCoeff w z‖ ≤ C := by
    exact Finset.single_le_sum (fun r _ => norm_nonneg (w r)) (Finset.mem_univ _)
  apply ((eisensteinComplexGaussian_summable ha).norm.mul_left C).of_norm_bounded
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg _)

/-- Translation of the lattice Gaussian by arbitrary real coordinates. -/
def eisensteinShiftedGaussian (a : ℂ) (x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * a *
    (((z.1 : ℂ) + x) ^ 2 - ((z.1 : ℂ) + x) * ((z.2 : ℂ) + y) +
      ((z.2 : ℂ) + y) ^ 2))

private theorem lattice_gaussian_summable_of_offset_re_bound (F : ℤ × ℤ → ℂ)
    {eps : ℝ} (heps : 0 < eps) (C : ℝ)
    (hbound : ∀ z : ℤ × ℤ,
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) - C ≤ (F z).re) :
    Summable (fun z : ℤ × ℤ => Complex.exp (-(Real.pi : ℂ) * F z)) := by
  have h1 := RankTwoPoisson.real_gauss_summable heps
  have hbase : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * eps * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * eps * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  apply (hbase.mul_left (Real.exp (Real.pi * C))).of_norm_bounded
  intro z
  have hb := mul_le_mul_of_nonneg_left (hbound z) Real.pi_pos.le
  have he : (-(Real.pi : ℂ) * F z).re ≤ Real.pi * C +
      (-Real.pi * eps * (z.1 : ℝ) ^ 2 + -Real.pi * eps * (z.2 : ℝ) ^ 2) := by
    simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, neg_zero,
      zero_mul, sub_zero]
    nlinarith
  simpa only [Complex.norm_exp, Real.exp_add] using Real.exp_le_exp.mpr he

theorem eisensteinShiftedGaussian_summable {a : ℂ} (ha : 0 < a.re) (x y : ℝ) :
    Summable (eisensteinShiftedGaussian a x y) := by
  have h := lattice_gaussian_summable_of_offset_re_bound
    (fun z : ℤ × ℤ => a *
      (((z.1 : ℂ) + x) ^ 2 - ((z.1 : ℂ) + x) * ((z.2 : ℂ) + y) +
        ((z.2 : ℂ) + y) ^ 2))
    (eps := a.re / 4) (by positivity) (a.re * (x ^ 2 + y ^ 2) / 2) ?_
  · convert h using 1
    ext z
    unfold eisensteinShiftedGaussian
    congr 1
    ring
  intro z
  have hq : (((z.1 : ℝ) + x) ^ 2 + ((z.2 : ℝ) + y) ^ 2) / 2 ≤
      ((z.1 : ℝ) + x) ^ 2 - ((z.1 : ℝ) + x) * ((z.2 : ℝ) + y) +
        ((z.2 : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg (((z.1 : ℝ) + x) - ((z.2 : ℝ) + y))]
  have hm : (z.1 : ℝ) ^ 2 / 2 - x ^ 2 ≤ ((z.1 : ℝ) + x) ^ 2 := by
    nlinarith [sq_nonneg ((z.1 : ℝ) + 2 * x)]
  have hn : (z.2 : ℝ) ^ 2 / 2 - y ^ 2 ≤ ((z.2 : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((z.2 : ℝ) + 2 * y)]
  have hb := mul_le_mul_of_nonneg_left hq ha.le
  have hm' := mul_le_mul_of_nonneg_left hm ha.le
  have hn' := mul_le_mul_of_nonneg_left hn ha.le
  simp [mul_re, mul_im, pow_two]
  nlinarith

private def shiftedConstant (a : ℂ) (x y : ℝ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * a * ((x : ℂ) ^ 2 - x * y + (y : ℂ) ^ 2))

private def shiftedU (a : ℂ) (x y : ℝ) : ℂ := -a * ((x : ℂ) - y / 2)
private def shiftedV (a : ℂ) (x y : ℝ) : ℂ := -a * ((y : ℂ) - x / 2)

private theorem shifted_eq_affine (a : ℂ) (x y : ℝ) (z : ℤ × ℤ) :
    eisensteinShiftedGaussian a x y z = shiftedConstant a x y *
      RankTwoAffine.binaryGaussian a (-a / 2) a (shiftedU a x y) (shiftedV a x y) z := by
  unfold eisensteinShiftedGaussian shiftedConstant RankTwoAffine.binaryGaussian shiftedU shiftedV
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem shifted_dual_term {a : ℂ} (ha : a ≠ 0) (x y : ℝ) (z : ℤ × ℤ) :
    shiftedConstant a x y *
      RankTwoAffine.dualGaussian a (-a / 2) a (shiftedU a x y) (shiftedV a x y) z =
      eisensteinComplexGaussian (4 / (3 * a)) (z.1, -z.2) *
        RankTwoEisShift.dualPhase z.1 z.2 x y := by
  unfold shiftedConstant RankTwoAffine.dualGaussian eisensteinComplexGaussian
    RankTwoEisShift.dualPhase shiftedU shiftedV
  rw [eisenstein_schur ha, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem shifted_middle_term {a : ℂ} (ha : a ≠ 0) (x y : ℝ) (z : ℤ × ℤ) :
    shiftedConstant a x y *
      RankTwoAffine.firstGaussian a (-a / 2) a (shiftedU a x y) (shiftedV a x y) z =
      Complex.exp (-(Real.pi : ℂ) * a⁻¹ * (z.1 : ℂ) ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (3 * a / 4) * ((z.2 : ℂ) + y) ^ 2) *
        RankTwoEisShift.middlePhase z.1 z.2 x y := by
  unfold shiftedConstant RankTwoAffine.firstGaussian RankTwoEisShift.middlePhase shiftedU shiftedV
  rw [eisenstein_schur ha, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem shifted_real_gauss_summable {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * ((n : ℝ) + y) ^ 2)) := by
  have hbase := RankTwoPoisson.real_gauss_summable (show 0 < t / 2 by positivity)
  apply (hbase.mul_left (Real.exp (Real.pi * t * y ^ 2))).of_norm_bounded
  intro n
  have hs : (n : ℝ) ^ 2 / 2 - y ^ 2 ≤ ((n : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) + 2 * y)]
  have hm := mul_le_mul_of_nonneg_left hs (mul_pos Real.pi_pos ht).le
  have he : -Real.pi * t * ((n : ℝ) + y) ^ 2 ≤
      Real.pi * t * y ^ 2 + -Real.pi * (t / 2) * (n : ℝ) ^ 2 := by nlinarith
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_add] using
    Real.exp_le_exp.mpr he

private theorem shifted_affine_middle_summable {a : ℂ} (ha : 0 < a.re) (x y : ℝ) :
    Summable (RankTwoAffine.firstGaussian a (-a / 2) a (shiftedU a x y) (shiftedV a x y)) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have h1 := RankTwoPoisson.real_gauss_summable (eisenstein_inv_re_pos ha)
  have h2 := shifted_real_gauss_summable (show 0 < 3 * a.re / 4 by positivity) y
  have hbase : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * a⁻¹.re * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (3 * a.re / 4) * ((z.2 : ℝ) + y) ^ 2)) :=
    h1.mul_of_nonneg h2 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hs : Summable (fun z : ℤ × ℤ => shiftedConstant a x y *
      RankTwoAffine.firstGaussian a (-a / 2) a (shiftedU a x y) (shiftedV a x y) z) := by
    apply hbase.of_norm_bounded
    intro z
    rw [shifted_middle_term ha0, norm_mul, norm_mul]
    simp [RankTwoEisShift.middlePhase, Complex.norm_exp, mul_re, mul_im, pow_two,
      div_eq_mul_inv]
  have hC : shiftedConstant a x y ≠ 0 := Complex.exp_ne_zero _
  convert hs.mul_left (shiftedConstant a x y)⁻¹ using 1
  ext z
  simp [hC]

private theorem shifted_affine_dual_summable {a : ℂ} (ha : 0 < a.re) (x y : ℝ) :
    Summable (RankTwoAffine.dualGaussian a (-a / 2) a (shiftedU a x y) (shiftedV a x y)) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hE : Summable (fun z : ℤ × ℤ => eisensteinComplexGaussian (4 / (3 * a)) (z.1, -z.2)) :=
    (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).summable_iff.mpr
      (eisensteinComplexGaussian_summable (eisenstein_dual_parameter_re ha))
  have hs : Summable (fun z : ℤ × ℤ => shiftedConstant a x y *
      RankTwoAffine.dualGaussian a (-a / 2) a (shiftedU a x y) (shiftedV a x y) z) := by
    apply hE.norm.of_norm_bounded
    intro z
    rw [shifted_dual_term ha0, norm_mul, RankTwoEisShift.dualPhase_norm, mul_one]
  have hC : shiftedConstant a x y ≠ 0 := Complex.exp_ne_zero _
  convert hs.mul_left (shiftedConstant a x y)⁻¹ using 1
  ext z
  simp [hC]

private theorem shifted_affine_original_summable {a : ℂ} (ha : 0 < a.re) (x y : ℝ) :
    Summable (RankTwoAffine.binaryGaussian a (-a / 2) a (shiftedU a x y) (shiftedV a x y)) := by
  have hs := (eisensteinShiftedGaussian_summable ha x y).congr (shifted_eq_affine a x y)
  have hC : shiftedConstant a x y ≠ 0 := Complex.exp_ne_zero _
  convert hs.mul_left (shiftedConstant a x y)⁻¹ using 1
  ext z
  simp [hC]

/-- Complex shifted Poisson summation, with no unproved convergence hypotheses. -/
theorem eisensteinShiftedGaussian_inversion {a : ℂ} (ha : 0 < a.re) (x y : ℝ) :
    (∑' z : ℤ × ℤ, eisensteinShiftedGaussian a x y z) =
      (2 / ((Real.sqrt 3 : ℂ) * a)) * ∑' z : ℤ × ℤ,
        eisensteinComplexGaussian (4 / (3 * a)) (z.1, -z.2) *
          RankTwoEisShift.dualPhase z.1 z.2 x y := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have h := RankTwoAffine.affine_gaussian_poisson ha (eisenstein_schur_re ha)
    (shifted_affine_original_summable ha x y) (shifted_affine_middle_summable ha x y)
    (shifted_affine_dual_summable ha x y)
  simp_rw [eisenstein_schur ha0] at h
  rw [eisenstein_inversion_prefactor ha0] at h
  simp_rw [shifted_eq_affine a x y]
  rw [tsum_mul_left, h, ← mul_assoc, mul_comm (shiftedConstant a x y), mul_assoc,
    ← tsum_mul_left]
  simp_rw [shifted_dual_term ha0]

private theorem gaussian_residue_term {N : ℕ} [NeZero N] (a : ℂ)
    (p : (Fin N × Fin N) × (ℤ × ℤ)) :
    eisensteinComplexGaussian a ((HeckeTheta.residueEquiv N).symm p) =
      eisensteinShiftedGaussian (a * (N : ℂ) ^ 2)
        ((p.1.1 : ℝ) / N) ((p.1.2 : ℝ) / N) p.2 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  change eisensteinComplexGaussian a
    (p.2.1 * (N : ℤ) + p.1.1, p.2.2 * (N : ℤ) + p.1.2) = _
  unfold eisensteinComplexGaussian eisensteinShiftedGaussian
  push_cast
  congr 1
  field_simp

theorem eisensteinWeightedGaussian_residue_sum {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {a : ℂ} (ha : 0 < a.re) :
    eisensteinWeightedGaussian w a = ∑ r : Fin N × Fin N,
      w r * ∑' z : ℤ × ℤ, eisensteinShiftedGaussian (a * (N : ℂ) ^ 2)
        ((r.1 : ℝ) / N) ((r.2 : ℝ) / N) z := by
  let F : (Fin N × Fin N) × (ℤ × ℤ) → ℂ := fun p =>
    w p.1 * eisensteinShiftedGaussian (a * (N : ℂ) ^ 2)
      ((p.1.1 : ℝ) / N) ((p.1.2 : ℝ) / N) p.2
  have hterm (p : (Fin N × Fin N) × (ℤ × ℤ)) :
      HeckeTheta.periodicCoeff w ((HeckeTheta.residueEquiv N).symm p) *
        eisensteinComplexGaussian a ((HeckeTheta.residueEquiv N).symm p) = F p := by
    simp only [HeckeTheta.periodicCoeff, Equiv.apply_symm_apply, gaussian_residue_term, F]
  have hs : Summable F := by
    have h := (HeckeTheta.residueEquiv N).symm.summable_iff.mpr
      (eisensteinWeightedGaussian_summable w ha)
    exact h.congr hterm
  unfold eisensteinWeightedGaussian
  rw [← (HeckeTheta.residueEquiv N).symm.tsum_eq]
  simp_rw [hterm]
  rw [hs.tsum_prod, tsum_fintype]
  simp only [F, tsum_mul_left]

private theorem scaled_parameter_re {N : ℕ} [NeZero N] {a : ℂ} (ha : 0 < a.re) :
    0 < (a * (N : ℂ) ^ 2).re := by
  simpa [mul_re, mul_im, pow_two] using
    (show 0 < a.re * ((N : ℝ) * N) by
      exact mul_pos ha (mul_pos (Nat.cast_pos.mpr (NeZero.pos N))
        (Nat.cast_pos.mpr (NeZero.pos N))))

/-- Finite Fourier transform of a residue weight, evaluated at an integer frequency. -/
def eisensteinResidueFourier {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (z : ℤ × ℤ) : ℂ :=
  ∑ r : Fin N × Fin N, w r *
    RankTwoEisShift.dualPhase z.1 z.2 ((r.1 : ℝ) / N) ((r.2 : ℝ) / N)

theorem eisensteinResidueFourier_norm_le {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (z : ℤ × ℤ) :
    ‖eisensteinResidueFourier w z‖ ≤ ∑ r, ‖w r‖ := by
  unfold eisensteinResidueFourier
  calc
    _ ≤ ∑ r : Fin N × Fin N, ‖w r *
        RankTwoEisShift.dualPhase z.1 z.2 ((r.1 : ℝ) / N) ((r.2 : ℝ) / N)‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_mul, RankTwoEisShift.dualPhase_norm, mul_one]

theorem eisensteinResidueFourier_gaussian_summable {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {a : ℂ} (ha : 0 < a.re) :
    Summable (fun z : ℤ × ℤ => eisensteinResidueFourier w z *
      eisensteinComplexGaussian a (z.1, -z.2)) := by
  have hG : Summable (fun z : ℤ × ℤ => eisensteinComplexGaussian a (z.1, -z.2)) :=
    (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).summable_iff.mpr
      (eisensteinComplexGaussian_summable ha)
  apply (hG.norm.mul_left (∑ r, ‖w r‖)).of_norm_bounded
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (eisensteinResidueFourier_norm_le w z) (norm_nonneg _)

/-- Exact Poisson transformation for every finite periodic weight. -/
theorem eisensteinWeightedGaussian_inversion {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {a : ℂ} (ha : 0 < a.re) :
    eisensteinWeightedGaussian w a =
      (2 / ((Real.sqrt 3 : ℂ) * (a * (N : ℂ) ^ 2))) *
        ∑' z : ℤ × ℤ, eisensteinResidueFourier w z *
          eisensteinComplexGaussian (4 / (3 * (a * (N : ℂ) ^ 2))) (z.1, -z.2) := by
  classical
  have hpar := scaled_parameter_re (N := N) ha
  have hG : Summable (fun z : ℤ × ℤ =>
      eisensteinComplexGaussian (4 / (3 * (a * (N : ℂ) ^ 2))) (z.1, -z.2)) :=
    (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).summable_iff.mpr
      (eisensteinComplexGaussian_summable (eisenstein_dual_parameter_re hpar))
  have hs (r : Fin N × Fin N) : Summable (fun z : ℤ × ℤ =>
      w r * (eisensteinComplexGaussian (4 / (3 * (a * (N : ℂ) ^ 2))) (z.1, -z.2) *
        RankTwoEisShift.dualPhase z.1 z.2 ((r.1 : ℝ) / N) ((r.2 : ℝ) / N))) := by
    apply Summable.mul_left
    apply hG.norm.of_norm_bounded
    intro z
    rw [norm_mul, RankTwoEisShift.dualPhase_norm, mul_one]
  rw [eisensteinWeightedGaussian_residue_sum w ha]
  simp_rw [eisensteinShiftedGaussian_inversion hpar]
  simp_rw [mul_left_comm (w _) (2 / ((Real.sqrt 3 : ℂ) * (a * (N : ℂ) ^ 2)))]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => hs r)]
  apply tsum_congr
  intro z
  simp only [eisensteinResidueFourier, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The periodic weighted Gaussian is the actual ideal theta series, with
the six Eisenstein units accounted for. -/
theorem eisensteinWeightedGaussian_eq_six_heckeTheta (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) (τ : ℍ) :
    eisensteinWeightedGaussian (HeckeFamily.coefficients χ) (eisensteinGaussianParameter τ) =
      6 * heckeTheta χ τ :=
  periodicGaussian_eq_six_heckeTheta χ hχ τ

/-- Poisson transformation of the actual nonprincipal Hecke theta series.
The dual finite Fourier weight is explicit; identifying its arithmetic
transformation law is not an assumption or a conclusion of this theorem. -/
theorem heckeTheta_weighted_poisson (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) (τ : ℍ) :
    6 * heckeTheta χ τ =
      (2 / ((Real.sqrt 3 : ℂ) *
        (eisensteinGaussianParameter τ * (χ.period : ℂ) ^ 2))) *
        ∑' z : ℤ × ℤ, eisensteinResidueFourier (HeckeFamily.coefficients χ) z *
          eisensteinComplexGaussian
            (4 / (3 * (eisensteinGaussianParameter τ * (χ.period : ℂ) ^ 2)))
            (z.1, -z.2) := by
  rw [← eisensteinWeightedGaussian_eq_six_heckeTheta χ hχ τ]
  exact eisensteinWeightedGaussian_inversion _ (eisensteinGaussianParameter_re τ)

end ArtinMatthews
