module

public import ArtinMatthews.SpectralPeterssonPeriodizedQExpansion
public import Mathlib.Analysis.SpecialFunctions.Bessel


set_option backward.privateInPublic true
@[expose] public section

/-! The literal factorial series of the local Petersson coefficient
is the existing Bessel J, with the original frequency and modulus. -/

noncomputable section

namespace ArtinMatthews

theorem spectralPetersson_besselJ_nat_factorial (l : ℕ) (X : ℂ) :
    Complex.besselJ (l : ℂ) X =
      (X/2)^l*(∑' j : ℕ, (-((X/2)^2))^j/((j.factorial : ℂ)*((l+j).factorial : ℂ))) := by
  rw [Complex.besselJ,Complex.cpow_natCast,Complex.regularizedHGFun,Complex.regularizedHGFunSeries,
    ← FormalMultilinearSeries.ofScalarsSum,FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  congr 1
  apply tsum_congr
  intro j
  have hg : Complex.Gamma ((l : ℂ)+1+(j : ℂ)) = ((l+j).factorial : ℂ) := by
    rw [show (l : ℂ)+1+(j : ℂ) = ((l+j : ℕ) : ℂ)+1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  simp [Complex.regularizedHGFunCoeff,hg,smul_eq_mul]
  ring

def spectralPeterssonWeylAlpha (m : ℕ+) (C : ℝ) : ℂ :=
  -2*(Real.pi : ℂ)*Complex.I*(m : ℂ)/(C : ℂ)^2

def spectralPeterssonBesselArgument (m n : ℕ+) (C : ℝ) : ℝ :=
  4*Real.pi*Real.sqrt ((m : ℝ)*(n : ℝ))/C

theorem spectralPeterssonPeriodizedCoefficient_bessel (l : ℕ) (m n : ℕ+) (C : ℝ)
    (hC : 0 < C) :
    spectralPeterssonPeriodizedCoefficient (l+1) (spectralPeterssonWeylAlpha m C) n/(C : ℂ)^(l+1) =
      (2*(Real.pi : ℂ)*Complex.I^(-((l+1 : ℕ) : ℤ))/(C : ℂ))*
        ((Real.sqrt ((n : ℝ)/(m : ℝ)) : ℝ) : ℂ)^l*
        Complex.besselJ (l : ℂ) (spectralPeterssonBesselArgument m n C : ℂ) := by
  let c : ℂ := C
  let p : ℂ := 2*(Real.pi : ℂ)
  let u : ℂ := -2*(Real.pi : ℂ)*Complex.I
  let t : ℂ := n
  let r : ℂ := ((2*Real.pi*Real.sqrt ((m : ℝ)*(n : ℝ))/C : ℝ) : ℂ)
  let s : ℂ := (Real.sqrt ((n : ℝ)/(m : ℝ)) : ℝ)
  let α := spectralPeterssonWeylAlpha m C
  let T := ∑' j : ℕ, (-(r^2))^j/((j.factorial : ℂ)*((l+j).factorial : ℂ))
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr m.property
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr n.property
  have hrR : (2*Real.pi*Real.sqrt ((m : ℝ)*(n : ℝ))/C)^2 =
      (2*Real.pi)^2*(m : ℝ)*(n : ℝ)/C^2 := by
    rw [div_pow,mul_pow,Real.sq_sqrt (mul_nonneg hm.le hn.le)]
    ring
  have hr2 : r^2 = p^2*(m : ℂ)*t/c^2 := by
    dsimp only [r,p,t,c]
    exact_mod_cast hrR
  have hu2 : u^2 = -(p^2) := by
    dsimp only [u]
    rw [mul_pow,Complex.I_sq]
    ring
  have hα : α*u*t = -(r^2) := by
    calc
      _ = u^2*(m : ℂ)*t/c^2 := by
        change (u*(m : ℂ)/c^2)*u*t = _
        ring
      _ = _ := by rw [hu2,hr2]; ring
  have hseries : spectralPeterssonPeriodizedCoefficient (l+1) α n = (u^(l+1)*t^l)*T := by
    unfold spectralPeterssonPeriodizedCoefficient
    dsimp only [T]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    change α^j/(j.factorial : ℂ)*
        (u^(l+1+j)/((l+1+j-1).factorial : ℂ))*t^(l+1+j-1) =
      (u^(l+1)*t^l)*((-(r^2))^j/((j.factorial : ℂ)*((l+j).factorial : ℂ)))
    rw [show l+1+j-1=l+j by omega, ← hα, pow_add u (l+1) j, pow_add t l j]
    simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  have hX : (spectralPeterssonBesselArgument m n C : ℂ)/2 = r := by
    unfold spectralPeterssonBesselArgument
    dsimp only [r]
    push_cast
    ring
  have hB : Complex.besselJ (l : ℂ) (spectralPeterssonBesselArgument m n C : ℂ) = r^l*T := by
    rw [spectralPetersson_besselJ_nat_factorial,hX]
  have hroot : Real.sqrt ((n : ℝ)/(m : ℝ))*Real.sqrt ((m : ℝ)*(n : ℝ)) = (n : ℝ) := by
    rw [Real.sqrt_div hn.le,Real.sqrt_mul hm.le]
    calc
      _ = Real.sqrt (n : ℝ)*Real.sqrt (n : ℝ) := by
        field_simp [(Real.sqrt_pos.mpr hm).ne'] <;> ring
      _ = _ := Real.mul_self_sqrt hn.le
  have hsr : s*r = p*t/c := by
    have h : Real.sqrt ((n : ℝ)/(m : ℝ))*
        (2*Real.pi*Real.sqrt ((m : ℝ)*(n : ℝ))/C) = (2*Real.pi)*(n : ℝ)/C := by
      rw [show Real.sqrt ((n : ℝ)/(m : ℝ))*(2*Real.pi*Real.sqrt ((m : ℝ)*(n : ℝ))/C) =
        (2*Real.pi)*(Real.sqrt ((n : ℝ)/(m : ℝ))*Real.sqrt ((m : ℝ)*(n : ℝ)))/C by ring,hroot]
    dsimp only [s,r,p,t,c]
    exact_mod_cast h
  have hscale : u^(l+1)*t^l/c^(l+1) =
      (p*Complex.I^(-((l+1 : ℕ) : ℤ))/c)*s^l*r^l := by
    have hu : u = p*Complex.I⁻¹ := by dsimp only [u]; rw [Complex.inv_I]; ring
    have hp : s^l*r^l = (p*t/c)^l := by rw [← mul_pow,hsr]
    rw [hu,mul_pow,zpow_neg,zpow_natCast,← inv_pow]
    calc
      _ = (p*(Complex.I⁻¹)^(l+1)/c)*(p*t/c)^l := by
        rw [div_pow,mul_pow p t l,pow_succ p l,pow_succ c l]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ = _ := by rw [← hp]; ring
  change spectralPeterssonPeriodizedCoefficient (l+1) α n/c^(l+1) =
    (p*Complex.I^(-((l+1 : ℕ) : ℤ))/c)*s^l*
      Complex.besselJ (l : ℂ) (spectralPeterssonBesselArgument m n C : ℂ)
  rw [hseries,hB]
  calc
    _ = (u^(l+1)*t^l/c^(l+1))*T := by ring
    _ = _ := by rw [hscale]; ring

end ArtinMatthews
