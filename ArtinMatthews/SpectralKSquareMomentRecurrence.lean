module

public import ArtinMatthews.SpectralKSquareMellinMoment


set_option backward.privateInPublic true
@[expose] public section

/-! Consecutive even moments of the actual real K kernel. This recurrence
uses the Gamma recurrence in the proved Mellin formula. -/

noncomputable section

namespace ArtinMatthews

theorem spectralKSquareMoment_succ (k : ℕ) (t : ℝ) :
    spectralKSquareMoment (k+1) t =
      (4*((k : ℝ)+1/2)^2*(((k : ℝ)+1/2)^2+t^2)/((2*(k : ℝ)+1)*(2*(k : ℝ)+2)))*
        spectralKSquareMoment k t := by
  let a := (k : ℂ)+1/2
  let s := 2*(k : ℂ)+1
  let ν := (t : ℂ)*Complex.I
  have ha0 : 0 < a.re := by
    dsimp only [a]
    norm_num [Complex.add_re,Complex.div_re]
    positivity
  have hs0 : 0 < s.re := by
    dsimp only [s]
    norm_num [Complex.add_re,Complex.mul_re]
    positivity
  have hν : ν.re = 0 := by simp [ν,Complex.mul_re]
  have hne (z : ℂ) (hz : 0 < z.re) : z ≠ 0 :=
    ne_of_apply_ne Complex.re (by simpa using hz.ne')
  have ha := hne a ha0
  have hm := hne (a-ν) (by simpa only [Complex.sub_re,hν,sub_zero] using ha0)
  have hp := hne (a+ν) (by simpa only [Complex.add_re,hν,add_zero] using ha0)
  have hs := hne s hs0
  have hs1 := hne (s+1) (by simp only [Complex.add_re,Complex.one_re]; linarith)
  have hg : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hk : ((k+1 : ℕ) : ℂ)+1/2 = a+1 := by dsimp only [a]; push_cast; ring
  have hks : 2*((k+1 : ℕ) : ℂ)+1 = s+2 := by dsimp only [s]; push_cast; ring
  have htwo : (2 : ℂ)^(s+2-3) = 4*(2 : ℂ)^(s-3) := by
    rw [show s+2-3 = (s-3)+((2 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ (by norm_num),Complex.cpow_natCast]
    ring
  have hden : Complex.Gamma (s+2) = (s+1)*(s*Complex.Gamma s) := by
    rw [show s+2=(s+1)+1 by ring,Complex.Gamma_add_one _ hs1,Complex.Gamma_add_one _ hs]
  have hM0 : (spectralKSquareMoment k t : ℂ) =
      (2 : ℂ)^(s-3)*Complex.Gamma (a-ν)*Complex.Gamma a^2*Complex.Gamma (a+ν)/Complex.Gamma s :=
    spectralKSquareMoment_closed k t
  have hM1 : (spectralKSquareMoment (k+1) t : ℂ) =
      (4*(2 : ℂ)^(s-3))*((a-ν)*Complex.Gamma (a-ν))*(a*Complex.Gamma a)^2*
        ((a+ν)*Complex.Gamma (a+ν))/((s+1)*(s*Complex.Gamma s)) := by
    rw [spectralKSquareMoment_closed]
    rw [hk,hks,htwo,hden,
      show a+1-ν=(a-ν)+1 by ring,show a+1+ν=(a+ν)+1 by ring,
      Complex.Gamma_add_one _ hm,Complex.Gamma_add_one _ hp,Complex.Gamma_add_one _ ha]
  have hpoly : (a-ν)*(a+ν) = a^2+(t : ℂ)^2 := by
    dsimp only [ν]
    linear_combination -((t : ℂ)^2)*Complex.I_sq
  have hcoeff :
      (((4*((k : ℝ)+1/2)^2*(((k : ℝ)+1/2)^2+t^2)/((2*(k : ℝ)+1)*(2*(k : ℝ)+2))) : ℝ) : ℂ) =
        4*a^2*(a^2+(t : ℂ)^2)/(s*(s+1)) := by
    dsimp only [a,s]
    push_cast
    ring
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,hcoeff,hM1,hM0,← hpoly]
  field_simp [hs,hs1,hg]

theorem spectralKSquareMoment_one (t : ℝ) :
    spectralKSquareMoment 1 t = ((t^2+1/4)/2)*spectralKSquareMoment 0 t := by
  change spectralKSquareMoment (0+1) t = _
  rw [spectralKSquareMoment_succ]
  congr 1
  norm_num
  ring

theorem spectralKSquareMoment_two (t : ℝ) :
    spectralKSquareMoment 2 t = ((3/4)*(t^2+9/4))*spectralKSquareMoment 1 t := by
  change spectralKSquareMoment (1+1) t = _
  rw [spectralKSquareMoment_succ]
  congr 1
  norm_num
  ring

end ArtinMatthews
