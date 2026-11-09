module

public import ArtinMatthews.SpectralEisensteinPowerCalculus
public import ArtinMatthews.SpectralEisensteinLogBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Same-decay first and second derivative bounds for every row power. -/
noncomputable section
namespace ArtinMatthews

private theorem eisenstein_complex_second_bound (F s : ℂ) (a b t A B C : ℝ)
    (ha : |a|≤A) (hb : |b|≤B) (ht : |t|≤C) :
    ‖F*(s^2*(a:ℂ)*(b:ℂ)+s*(t:ℂ))‖ ≤ ‖F‖*(‖s‖^2*A*B+‖s‖*C) := by
  have hAB : |a| *|b| ≤ A*B := mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  calc
    _ = ‖F‖*‖s^2*(a:ℂ)*(b:ℂ)+s*(t:ℂ)‖ := norm_mul _ _
    _ ≤ ‖F‖*(‖s^2*(a:ℂ)*(b:ℂ)‖+‖s*(t:ℂ)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = ‖F‖*(‖s‖^2*(|a| *|b|)+‖s‖*|t|) := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      ring
    _ ≤ ‖F‖*(‖s‖^2*(A*B)+‖s‖*C) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hAB (sq_nonneg _))
        (mul_le_mul_of_nonneg_left ht (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

theorem eisensteinRowPowerX_bound (s : ℂ) (c d : ℝ) (hcd : c≠0 ∨ d≠0)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    ‖eisensteinRowPowerX s c d p‖ ≤ (2*‖s‖/p.2)*‖eisensteinRowPower s c d p‖ := by
  rw [eisensteinRowPowerX,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ (‖s‖*‖eisensteinRowPower s c d p‖)*(2/p.2) :=
      mul_le_mul_of_nonneg_left (eisensteinRowLogX_bound c d hcd p hp) (by positivity)
    _ = _ := by ring

theorem eisensteinRowPowerY_bound (s : ℂ) (c d : ℝ) (hcd : c≠0 ∨ d≠0)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    ‖eisensteinRowPowerY s c d p‖ ≤ (3*‖s‖/p.2)*‖eisensteinRowPower s c d p‖ := by
  rw [eisensteinRowPowerY,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ (‖s‖*‖eisensteinRowPower s c d p‖)*(3/p.2) :=
      mul_le_mul_of_nonneg_left (eisensteinRowLogY_bound c d hcd p hp) (by positivity)
    _ = _ := by ring

theorem eisensteinRowPowerXX_bound (s : ℂ) (c d : ℝ) (hcd : c≠0 ∨ d≠0)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    ‖eisensteinRowPowerXX s c d p‖ ≤
      ((4*‖s‖^2+6*‖s‖)/p.2^2)*‖eisensteinRowPower s c d p‖ := by
  have h := eisenstein_complex_second_bound (eisensteinRowPower s c d p) s
    (eisensteinRowLogX c d p) (eisensteinRowLogX c d p) (eisensteinRowLogXX c d p)
    (2/p.2) (2/p.2) (6/p.2^2) (eisensteinRowLogX_bound c d hcd p hp)
    (eisensteinRowLogX_bound c d hcd p hp) (eisensteinRowLogXX_bound c d hcd p hp)
  rw [show ‖eisensteinRowPower s c d p‖*(‖s‖^2*(2/p.2)*(2/p.2)+‖s‖*(6/p.2^2)) =
      ((4*‖s‖^2+6*‖s‖)/p.2^2)*‖eisensteinRowPower s c d p‖ by ring] at h
  simpa only [eisensteinRowPowerXX,pow_two,mul_assoc] using h

theorem eisensteinRowPowerXY_bound (s : ℂ) (c d : ℝ) (hcd : c≠0 ∨ d≠0)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    ‖eisensteinRowPowerXY s c d p‖ ≤
      ((6*‖s‖^2+4*‖s‖)/p.2^2)*‖eisensteinRowPower s c d p‖ := by
  have h := eisenstein_complex_second_bound (eisensteinRowPower s c d p) s
    (eisensteinRowLogX c d p) (eisensteinRowLogY c d p) (eisensteinRowLogXY c d p)
    (2/p.2) (3/p.2) (4/p.2^2) (eisensteinRowLogX_bound c d hcd p hp)
    (eisensteinRowLogY_bound c d hcd p hp) (eisensteinRowLogXY_bound c d hcd p hp)
  rw [show ‖eisensteinRowPower s c d p‖*(‖s‖^2*(2/p.2)*(3/p.2)+‖s‖*(4/p.2^2)) =
      ((6*‖s‖^2+4*‖s‖)/p.2^2)*‖eisensteinRowPower s c d p‖ by ring] at h
  exact h

theorem eisensteinRowPowerYY_bound (s : ℂ) (c d : ℝ) (hcd : c≠0 ∨ d≠0)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    ‖eisensteinRowPowerYY s c d p‖ ≤
      ((9*‖s‖^2+7*‖s‖)/p.2^2)*‖eisensteinRowPower s c d p‖ := by
  have h := eisenstein_complex_second_bound (eisensteinRowPower s c d p) s
    (eisensteinRowLogY c d p) (eisensteinRowLogY c d p) (eisensteinRowLogYY c d p)
    (3/p.2) (3/p.2) (7/p.2^2) (eisensteinRowLogY_bound c d hcd p hp)
    (eisensteinRowLogY_bound c d hcd p hp) (eisensteinRowLogYY_bound c d hcd p hp)
  rw [show ‖eisensteinRowPower s c d p‖*(‖s‖^2*(3/p.2)*(3/p.2)+‖s‖*(7/p.2^2)) =
      ((9*‖s‖^2+7*‖s‖)/p.2^2)*‖eisensteinRowPower s c d p‖ by ring] at h
  simpa only [eisensteinRowPowerYY,pow_two,mul_assoc] using h

theorem eisensteinRowPower_fderiv_bound (s : ℂ) (c d : ℝ) (hcd : c≠0 ∨ d≠0)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    ‖fderiv ℝ (eisensteinRowPower s c d) p‖ ≤
      (5*‖s‖/p.2)*‖eisensteinRowPower s c d p‖ := by
  rw [(eisensteinRowPower_hasFDerivAt s c d hcd p hp).fderiv]
  exact (spectralPlaneDerivative_norm_le _ _).trans
    ((add_le_add (eisensteinRowPowerX_bound s c d hcd p hp)
      (eisensteinRowPowerY_bound s c d hcd p hp)).trans_eq (by ring))

theorem eisensteinRowPower_second_bound (s : ℂ) (c d : ℝ) (hcd : c≠0 ∨ d≠0)
    (p : ℝ × ℝ) (hp : 0<p.2) :
    ‖fderiv ℝ (fderiv ℝ (eisensteinRowPower s c d)) p‖ ≤
      ((50*‖s‖^2+42*‖s‖)/p.2^2)*‖eisensteinRowPower s c d p‖ := by
  rw [eisensteinRowPower_second s c d hcd p hp]
  apply (spectralPlaneDerivativeMap_derivative_norm_le _ _).trans
  have hxx := eisensteinRowPowerXX_bound s c d hcd p hp
  have hxy := eisensteinRowPowerXY_bound s c d hcd p hp
  have hyy := eisensteinRowPowerYY_bound s c d hcd p hp
  have h1 := (spectralPlaneDerivative_norm_le _ _).trans (add_le_add hxx hxy)
  have h2 := (spectralPlaneDerivative_norm_le _ _).trans (add_le_add hxy hyy)
  exact (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

end ArtinMatthews
