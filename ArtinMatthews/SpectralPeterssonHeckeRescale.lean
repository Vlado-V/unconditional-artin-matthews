module

public import ArtinMatthews.SpectralPeterssonHeckeSeed
public import ArtinMatthews.SpectralPeterssonHeckeProfile


set_option backward.privateInPublic true
@[expose] public section

/-! Exact rescaling of a positive-modulus regulated Weyl summand.
The regulator is evaluated on the transformed height. -/

noncomputable section
open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

theorem spectralHolomorphicSlash_realTranslation (k : ℕ) (t : ℝ) (F : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) :
    spectralHolomorphicSlash k (realTranslation t) F z = F (realTranslation t • z) := by
  rw [spectralHolomorphicSlash_apply]
  have h : (((realTranslation t 1 0 : ℝ) : ℂ)*(z : ℂ)+((realTranslation t 1 1 : ℝ) : ℂ)) = 1 := by
    simp [realTranslation]
  rw [h,one_pow,div_one]

private theorem peterssonHecke_bruhat_point (G : SL(2, ℝ)) (z : UpperHalfPlane) (hC : G 1 0 ≠ 0) :
    ((G • z : UpperHalfPlane) : ℂ) =
      ((G 0 0 : ℝ) : ℂ)/((G 1 0 : ℝ) : ℂ)-
        1/((((G 1 0 : ℝ) : ℂ)^2)*((z : ℂ)+((G 1 1 : ℝ) : ℂ)/((G 1 0 : ℝ) : ℂ))) := by
  let A : ℂ := G 0 0
  let B : ℂ := G 0 1
  let C : ℂ := G 1 0
  let D : ℂ := G 1 1
  have hc : C ≠ 0 := Complex.ofReal_ne_zero.mpr hC
  have hdetR : G 0 0*G 1 1-G 0 1*G 1 0=1 := by
    simpa only [Matrix.det_fin_two] using G.det_coe
  have hdet : A*D-B*C=1 := by dsimp only [A,B,C,D]; exact_mod_cast hdetR
  have hd : C*(z : ℂ)+D ≠ 0 := by
    simpa [UpperHalfPlane.denom,C,D] using UpperHalfPlane.denom_ne_zero
      (Matrix.SpecialLinearGroup.mapGL ℝ G) z
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply]
  change (A*(z : ℂ)+B)/(C*(z : ℂ)+D) = A/C-1/(C^2*((z : ℂ)+D/C))
  have hdenom : C^2*((z : ℂ)+D/C) = C*(C*(z : ℂ)+D) := by field_simp [hc]
  rw [hdenom]
  apply (div_eq_iff hd).mpr
  have hfrac : (1/(C*(C*(z : ℂ)+D)))*(C*(z : ℂ)+D)=1/C := by
    field_simp [hc,hd]
  rw [sub_mul,hfrac]
  field_simp [hc]
  linear_combination -hdet

def spectralPeterssonHeckeLambda (m : ℕ+) (C y : ℝ) : ℝ := 2*Real.pi*(m : ℝ)/(C^2*y)

theorem spectralPeterssonHeckeSlash_rescale (u : ℝ) (m : ℕ+) (G : SL(2, ℝ))
    (hC : 0 < G 1 0) (z : UpperHalfPlane) :
    let C := G 1 0
    let y := z.im
    spectralHolomorphicSlash 2 G (spectralPeterssonHeckeSeed u m) z =
      (atkinPhase ((m : ℝ)*G 0 0/C)*((C^(-(2+2*u))*y^(-2-u) : ℝ) : ℂ))*
        spectralPeterssonHeckeProfile u (spectralPeterssonHeckeLambda m C y) ((z.re+G 1 1/C)/y) := by
  let A := G 0 0
  let C := G 1 0
  let D := G 1 1
  let y := z.im
  let t := (z.re+D/C)/y
  let w : ℂ := (t : ℂ)+Complex.I
  let R := 1+t^2
  have hCpos : 0 < C := hC
  have hy : 0 < y := z.im_pos
  have hR : 0 < R := by dsimp only [R]; positivity
  have hC' : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hnorm : ‖w‖^2 = R := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,w,R,pow_two,add_comm]
  have hz : (z : ℂ)+((D/C : ℝ) : ℂ) = (y : ℂ)*w := by
    have ht : (y : ℂ)*(t : ℂ) = (z.re : ℂ)+((D/C : ℝ) : ℂ) := by
      dsimp only [t]
      push_cast
      field_simp [hy']
    have hz : (z : ℂ) = (z.re : ℂ)+(y : ℂ)*Complex.I := (Complex.re_add_im (z : ℂ)).symm
    change _ = (y : ℂ)*((t : ℂ)+Complex.I)
    rw [hz,mul_add,ht]
    ring
  have hd : (C : ℂ)*(z : ℂ)+(D : ℂ) = ((C*y : ℝ) : ℂ)*w := by
    rw [Complex.ofReal_mul,mul_assoc,← hz,mul_add,Complex.ofReal_div]
    field_simp [hC']
  have hpoint : ((G • z : UpperHalfPlane) : ℂ) = ((A/C : ℝ) : ℂ)-1/((C : ℂ)^2*(y : ℂ)*w) := by
    have h := peterssonHecke_bruhat_point G z hC.ne'
    change ((G • z : UpperHalfPlane) : ℂ) = (A : ℂ)/(C : ℂ)-1/((C : ℂ)^2*((z : ℂ)+(D : ℂ)/(C : ℂ))) at h
    rw [← Complex.ofReal_div,← Complex.ofReal_div,hz,← mul_assoc] at h
    exact h
  have hi : (G • z).im = (C^2*y*R)⁻¹ := by
    rw [spectralPeterssonHecke_im]
    change y/‖(C : ℂ)*(z : ℂ)+(D : ℂ)‖^2 = _
    rw [hd,norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hCpos.le hy.le),hnorm]
    field_simp [hCpos.ne',hy.ne',hR.ne']
  have hipow : (G • z).im^u = C^(-(2*u))*y^(-u)*R^(-u) := by
    rw [hi,Real.inv_rpow (by positivity : 0 ≤ C^2*y*R),← Real.rpow_neg (by positivity : 0 ≤ C^2*y*R),
      Real.mul_rpow (by positivity : 0 ≤ C^2*y) hR.le,Real.mul_rpow (by positivity : 0 ≤ C^2) hy.le,
      ← Real.rpow_natCast_mul hCpos.le 2 (-u)]
    congr 2
    push_cast
    ring
  have hcoef : (G • z).im^u/(C*y)^2 = C^(-(2+2*u))*y^(-2-u)*R^(-u) := by
    rw [hipow,show -(2+2*u)=-(2*u)-2 by ring,show -2-u=-u-2 by ring,
      Real.rpow_sub hCpos,Real.rpow_sub hy,Real.rpow_two,Real.rpow_two,mul_pow]
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  have hE : Complex.exp (2*(Real.pi : ℂ)*Complex.I*(m : ℂ)*(((A/C : ℝ) : ℂ)-1/((C : ℂ)^2*(y : ℂ)*w))) =
      atkinPhase ((m : ℝ)*A/C)*Complex.exp (-Complex.I*(spectralPeterssonHeckeLambda m C y : ℂ)/w) := by
    unfold atkinPhase spectralPeterssonHeckeLambda
    rw [← Complex.exp_add]
    congr 1
    push_cast
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  dsimp only
  rw [spectralHolomorphicSlash_apply,spectralPeterssonHeckeSeed,spectralHolomorphicCuspSeed,hpoint,hE,hd,
    mul_pow,spectralPeterssonHeckeProfile_eq]
  change (((G • z).im^u : ℝ) : ℂ)*
      (atkinPhase ((m : ℝ)*A/C)*Complex.exp (-Complex.I*(spectralPeterssonHeckeLambda m C y : ℂ)/w))/
      (((C*y : ℝ) : ℂ)^2*w^2) =
      (atkinPhase ((m : ℝ)*A/C)*((C^(-(2+2*u))*y^(-2-u) : ℝ) : ℂ))*
        (Complex.exp (-Complex.I*(spectralPeterssonHeckeLambda m C y : ℂ)/w)*(w^2)⁻¹*
          ((R^(-u) : ℝ) : ℂ))
  calc
    _ = (((G • z).im^u/(C*y)^2 : ℝ) : ℂ)*
        (atkinPhase ((m : ℝ)*A/C)*Complex.exp (-Complex.I*(spectralPeterssonHeckeLambda m C y : ℂ)/w))*(w^2)⁻¹ := by
      push_cast
      simp only [div_eq_mul_inv,_root_.mul_inv_rev]
      ring
    _ = _ := by rw [hcoef]; push_cast; ring

end ArtinMatthews
