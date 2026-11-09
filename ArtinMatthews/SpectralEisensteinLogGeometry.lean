module

public import ArtinMatthews.SpectralPlaneDerivativeMap
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv


set_option backward.privateInPublic true
@[expose] public section

/-! Exact first and second derivatives of the logarithmic Eisenstein height. -/
noncomputable section
open Set
open scoped ContDiff
namespace ArtinMatthews

def eisensteinRowQuadratic (c d : ℝ) (p : ℝ × ℝ) : ℝ :=
  (c*p.1+d)^2+(c*p.2)^2

theorem eisensteinRowQuadratic_pos (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) : 0 < eisensteinRowQuadratic c d p := by
  rcases hcd with hc | hd
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (mul_ne_zero hc hp.ne'))
  · by_cases hc : c = 0
    · simp only [eisensteinRowQuadratic,hc,zero_mul,zero_add,ne_eq,hd,not_false_eq_true,
        sq_pos_of_ne_zero,zero_pow,OfNat.ofNat_ne_zero,add_zero]
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (mul_ne_zero hc hp.ne'))

theorem eisensteinRowQuadratic_hasFDerivAt (c d : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (eisensteinRowQuadratic c d)
      (spectralPlaneDerivative (2*c*(c*p.1+d)) (2*c^2*p.2)) p := by
  have ha := ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_mul c).add_const d
  have hb := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_mul c
  change HasFDerivAt (fun q : ℝ × ℝ => (c*q.1+d)^2+(c*q.2)^2) _ p
  convert! (ha.pow 2).add (hb.pow 2) using 1
  apply ContinuousLinearMap.ext
  intro h
  simp [spectralPlaneDerivative]
  ring

def eisensteinRowLog (c d : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.log p.2-Real.log (eisensteinRowQuadratic c d p)

def eisensteinRowLogX (c d : ℝ) (p : ℝ × ℝ) : ℝ :=
  -(2*c*(c*p.1+d))/eisensteinRowQuadratic c d p

def eisensteinRowLogY (c d : ℝ) (p : ℝ × ℝ) : ℝ :=
  1/p.2-(2*c^2*p.2)/eisensteinRowQuadratic c d p

def eisensteinRowLogXX (c d : ℝ) (p : ℝ × ℝ) : ℝ :=
  -(2*c^2)/eisensteinRowQuadratic c d p+
    (4*c^2*(c*p.1+d)^2)/(eisensteinRowQuadratic c d p)^2

def eisensteinRowLogXY (c d : ℝ) (p : ℝ × ℝ) : ℝ :=
  (4*c^3*(c*p.1+d)*p.2)/(eisensteinRowQuadratic c d p)^2

def eisensteinRowLogYY (c d : ℝ) (p : ℝ × ℝ) : ℝ :=
  -(1/p.2^2)-(2*c^2)/eisensteinRowQuadratic c d p+
    (4*c^4*p.2^2)/(eisensteinRowQuadratic c d p)^2

theorem eisensteinRowLog_hasFDerivAt (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinRowLog c d)
      (spectralPlaneDerivative (eisensteinRowLogX c d p) (eisensteinRowLogY c d p)) p := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  have h := ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).log hp.ne').sub
    ((eisensteinRowQuadratic_hasFDerivAt c d p).log hq.ne')
  change HasFDerivAt (fun q : ℝ × ℝ => Real.log q.2-Real.log (eisensteinRowQuadratic c d q)) _ p
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [eisensteinRowLogX,eisensteinRowLogY,spectralPlaneDerivative]
  field_simp
  ring

theorem eisensteinRowLogX_hasFDerivAt (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinRowLogX c d)
      (spectralPlaneDerivative (eisensteinRowLogXX c d p) (eisensteinRowLogXY c d p)) p := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  have hn := (((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_mul c).add_const d).const_mul (-(2*c))
  have hi := (hasDerivAt_inv hq.ne').comp_hasFDerivAt p (eisensteinRowQuadratic_hasFDerivAt c d p)
  have h := hn.mul hi
  convert! h using 1
  · funext u
    dsimp only [eisensteinRowLogX]
    simp only [div_eq_mul_inv,Function.comp_apply,Pi.mul_apply]
    ring
  · apply ContinuousLinearMap.ext
    intro u
    simp [eisensteinRowLogXX,eisensteinRowLogXY,spectralPlaneDerivative]
    field_simp
    ring

theorem eisensteinRowLogY_hasFDerivAt (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    HasFDerivAt (eisensteinRowLogY c d)
      (spectralPlaneDerivative (eisensteinRowLogXY c d p) (eisensteinRowLogYY c d p)) p := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  have hfirst := (hasDerivAt_inv hp.ne').comp_hasFDerivAt p (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hi := (hasDerivAt_inv hq.ne').comp_hasFDerivAt p (eisensteinRowQuadratic_hasFDerivAt c d p)
  have hsecond := ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_mul (2*c^2)).mul hi
  convert! hfirst.sub hsecond using 1
  · funext u
    dsimp only [eisensteinRowLogY]
    simp only [div_eq_mul_inv,one_mul,Function.comp_apply,Pi.sub_apply,Pi.mul_apply]
  · apply ContinuousLinearMap.ext
    intro u
    simp [eisensteinRowLogXY,eisensteinRowLogYY,spectralPlaneDerivative]
    field_simp
    ring

theorem eisensteinRowLog_eikonal (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    (eisensteinRowLogX c d p)^2+(eisensteinRowLogY c d p)^2 = 1/p.2^2 := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  unfold eisensteinRowLogX eisensteinRowLogY
  field_simp
  simp only [eisensteinRowQuadratic]
  ring

theorem eisensteinRowLog_laplacian (c d : ℝ) (hcd : c ≠ 0 ∨ d ≠ 0)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    eisensteinRowLogXX c d p+eisensteinRowLogYY c d p = -(1/p.2^2) := by
  have hq := eisensteinRowQuadratic_pos c d hcd p hp
  unfold eisensteinRowLogXX eisensteinRowLogYY
  field_simp
  simp only [eisensteinRowQuadratic]
  ring

end ArtinMatthews
