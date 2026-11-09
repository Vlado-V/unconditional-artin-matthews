module

public import ArtinMatthews.SpectralEisensteinRadialFlux


set_option backward.privateInPublic true
@[expose] public section

/-! Incoming and outgoing height powers have opposite imaginary currents
on the critical line. The mixed current cancels by exact conjugation. -/
noncomputable section
open scoped InnerProductSpace
namespace ArtinMatthews

theorem eisensteinCriticalParameter_conj {s : ℂ} (hs : s.re=1/2) :
    1-s=(starRingEnd ℂ) s := by
  apply Complex.ext
  · simp only [Complex.sub_re,Complex.one_re,Complex.conj_re]
    linarith
  · simp

theorem eisensteinCriticalParameter_real {s : ℂ} (hs : s.re=1/2) :
    (s*(1-s)).im=0 := by
  rw [eisensteinCriticalParameter_conj hs,Complex.mul_conj',← Complex.ofReal_pow,Complex.ofReal_im]

theorem spectralConjugatePair_current (s a b : ℂ) :
    ((starRingEnd ℂ) (a+b)*(s*a+(starRingEnd ℂ) s*b)).im =
      s.im*(‖a‖^2-‖b‖^2) := by
  let C := (starRingEnd ℂ) a*(starRingEnd ℂ) s*b
  have hC : (starRingEnd ℂ) C=(starRingEnd ℂ) b*s*a := by
    dsimp [C]
    simp only [map_mul,starRingEnd_self_apply]
    ring
  have he : (starRingEnd ℂ) (a+b)*(s*a+(starRingEnd ℂ) s*b)=
      (‖a‖:ℂ)^2*s+(‖b‖:ℂ)^2*(starRingEnd ℂ) s+C+(starRingEnd ℂ) C := by
    rw [hC,← Complex.mul_conj' a,← Complex.mul_conj' b,map_add]
    dsimp [C]
    ring
  rw [he,← Complex.ofReal_pow,← Complex.ofReal_pow]
  simp only [Complex.add_im,Complex.mul_im,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero]
  ring

theorem eisensteinCriticalPower_norm_sq {s : ℂ} (hs : s.re=1/2) {t : ℝ} (ht : 0<t) :
    ‖(t:ℂ)^s‖^2=t := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,hs,← Real.sqrt_eq_rpow,Real.sq_sqrt ht.le]

theorem eisensteinCriticalPower_pair_flux {s : ℂ} (hs : s.re=1/2) {t : ℝ} (ht : 0<t) (a b : ℂ) :
    (inner ℂ (a*(t:ℂ)^s+b*(t:ℂ)^(1-s))
      (a*(s*(t:ℂ)^(s-1))+b*((1-s)*(t:ℂ)^(1-s-1)))).im=
      s.im*(‖a‖^2-‖b‖^2) := by
  let A := a*(t:ℂ)^s
  let B := b*(t:ℂ)^(1-s)
  have hn : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hd : a*(s*(t:ℂ)^(s-1))+b*((1-s)*(t:ℂ)^(1-s-1))=
      (t:ℂ)⁻¹*(s*A+(starRingEnd ℂ) s*B) := by
    rw [Complex.cpow_sub s 1 hn,Complex.cpow_sub (1-s) 1 hn,Complex.cpow_one,
      ← eisensteinCriticalParameter_conj hs]
    dsimp only [A,B]
    simp only [div_eq_mul_inv]
    ring
  have hA : ‖A‖^2=‖a‖^2*t := by
    dsimp only [A]
    rw [norm_mul,mul_pow,eisensteinCriticalPower_norm_sq hs ht]
  have hB : ‖B‖^2=‖b‖^2*t := by
    have hq : (1-s).re=1/2 := by simp only [Complex.sub_re,Complex.one_re];linarith
    dsimp only [B]
    rw [norm_mul,mul_pow,eisensteinCriticalPower_norm_sq hq ht]
  rw [hd]
  change (inner ℂ (A+B) ((t:ℂ)⁻¹*(s*A+(starRingEnd ℂ) s*B))).im=_
  rw [show inner ℂ (A+B) ((t:ℂ)⁻¹*(s*A+(starRingEnd ℂ) s*B)) =
      (t:ℂ)⁻¹*((starRingEnd ℂ) (A+B)*(s*A+(starRingEnd ℂ) s*B)) by
        rw [RCLike.inner_apply];ring,
    ← Complex.ofReal_inv,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
    spectralConjugatePair_current,hA,hB]
  field_simp [ht.ne']

end ArtinMatthews
