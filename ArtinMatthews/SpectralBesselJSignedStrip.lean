module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselJAllX
public import ArtinMatthews.SpectralBesselJSpatialODE
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

/-! A signed real-order strip on a compact positive argument interval.
Two exact contiguous steps reduce it to the checked all-X Poisson bound. -/
noncomputable section
open Set Complex

namespace ArtinMatthews

theorem spectral_besselJ_signed_strip_on_Icc {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ c t x : ℝ, |c| ≤ 3/2 → x ∈ Icc a b →
      ‖Complex.besselJ ((c : ℂ)+2*(t : ℂ)*I) (x : ℂ)‖ ≤
        C*(1+|t|)^3*Real.exp (Real.pi*|t|) := by
  obtain ⟨C,hC,hJ⟩ := spectral_besselJ_closed_strip_allX 5 (by norm_num)
  let L := max 1 b
  let C₀ := C*L^5
  let D := 8/a
  have hL : 1 ≤ L := le_max_left _ _
  have hC₀ : 0 < C₀ := mul_pos hC (pow_pos (zero_lt_one.trans_le hL) _)
  have hD : 0 < D := div_pos (by norm_num) ha
  refine ⟨C₀*(D^2+D+1), by positivity, ?_⟩
  intro c t x hc hx
  let ν : ℂ := (c : ℂ)+2*(t : ℂ)*I
  let T := 1+|t|
  let E := Real.exp (Real.pi*|t|)
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hE : 0 < E := Real.exp_pos _
  have hx₀ : 0 < x := ha.trans_le hx.1
  have hJplus (d : ℝ) (hd : 0 ≤ d) (hd₁ : d ≤ 5) :
      ‖Complex.besselJ ((d : ℂ)+2*(t : ℂ)*I) (x : ℂ)‖ ≤ C₀*T*E := by
    have hpow : x^d ≤ L^5 := by
      calc
        _ ≤ L^d := Real.rpow_le_rpow hx₀.le (hx.2.trans (le_max_right _ _)) hd
        _ ≤ L^(5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL hd₁
        _ = _ := by norm_cast
    calc
      _ ≤ C*T*E*x^d := hJ d t x hd hd₁ hx₀
      _ ≤ C*T*E*L^5 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by dsimp only [C₀]; ring
  have hJ₂ : ‖Complex.besselJ (ν+2) (x : ℂ)‖ ≤ C₀*T*E := by
    rw [show ν+2 = ((c+2 : ℝ) : ℂ)+2*(t : ℂ)*I by dsimp [ν]; push_cast; ring]
    exact hJplus _ (by linarith only [(abs_le.mp hc).1]) (by linarith only [(abs_le.mp hc).2])
  have hJ₃ : ‖Complex.besselJ (ν+3) (x : ℂ)‖ ≤ C₀*T*E := by
    rw [show ν+3 = ((c+3 : ℝ) : ℂ)+2*(t : ℂ)*I by dsimp [ν]; push_cast; ring]
    exact hJplus _ (by linarith only [(abs_le.mp hc).1]) (by linarith only [(abs_le.mp hc).2])
  have hA (j : ℝ) (hj : 0 ≤ j) (hj₂ : j ≤ 2) : ‖2*(ν+(j : ℂ))/(x : ℂ)‖ ≤ D*T := by
    have hn : ‖ν+(j : ℂ)‖ ≤ 4*T := by
      rw [show ν+(j : ℂ) = ((c+j : ℝ) : ℂ)+2*(t : ℂ)*I by dsimp [ν]; push_cast; ring]
      calc
        _ ≤ ‖((c+j : ℝ) : ℂ)‖ + ‖2*(t : ℂ)*I‖ := norm_add_le _ _
        _ = |c+j|+2*|t| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          simp [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        _ ≤ 4*T := by
          dsimp only [T]
          linarith only [abs_add_le c j, abs_of_nonneg hj, hc, hj₂, abs_nonneg t]
    calc
      _ = 2*‖ν+(j : ℂ)‖/x := by
        rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg hx₀.le]
        norm_num
      _ ≤ (2*(4*T))/x := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hn (by norm_num)) hx₀.le
      _ ≤ (2*(4*T))/a := by gcongr; exact hx.1
      _ = _ := by dsimp only [D]; ring
  let A₁ := 2*(ν+1)/(x : ℂ)
  let A₂ := 2*(ν+2)/(x : ℂ)
  let J₂ := Complex.besselJ (ν+2) (x : ℂ)
  let J₃ := Complex.besselJ (ν+3) (x : ℂ)
  have hA₁ : ‖A₁‖ ≤ D*T := by simpa only [A₁,Complex.ofReal_one] using hA 1 (by norm_num) (by norm_num)
  have hA₂ : ‖A₂‖ ≤ D*T := by simpa only [A₂,Complex.ofReal_ofNat] using hA 2 (by norm_num) (by norm_num)
  have hRec : Complex.besselJ ν (x : ℂ) = A₁*A₂*J₂ - A₁*J₃ - J₂ := by
    rw [spectral_besselJ_order_recurrence ν hx₀, spectral_besselJ_order_recurrence (ν+1) hx₀,
      show ν+1+1 = ν+2 by ring, show ν+1+2 = ν+3 by ring]
    dsimp only [A₁,A₂,J₂,J₃]
    ring
  have hT₂ : T^2 ≤ T^3 := pow_le_pow_right₀ hT (by decide)
  have hT₁ : T ≤ T^3 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hT (by decide : 1 ≤ 3))
  change ‖Complex.besselJ ν (x : ℂ)‖ ≤ C₀*(D^2+D+1)*T^3*E
  calc
    _ ≤ ‖A₁*A₂*J₂‖ + ‖A₁*J₃‖ + ‖J₂‖ := by
      rw [hRec]
      exact (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ (D*T)*(D*T)*(C₀*T*E) + (D*T)*(C₀*T*E) + C₀*T*E := by
      simp only [norm_mul]
      gcongr <;> assumption
    _ = D^2*C₀*T^3*E + D*C₀*T^2*E + C₀*T*E := by ring
    _ ≤ D^2*C₀*T^3*E + D*C₀*T^3*E + C₀*T^3*E := by gcongr
    _ = _ := by ring

end ArtinMatthews
