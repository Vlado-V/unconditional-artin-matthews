module

public import ArtinMatthews.SpectralABLCorrectedWindows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex
open scoped BigOperators
noncomputable section

/-- Gamma recurrence absorbs the literal pole-cancelling product. -/
def spectralABLExceptionalWideGamma (A : ℕ) (z : ℂ) : ℂ :=
  Complex.Gamma ((A : ℂ)+3/2+I*z)*Complex.Gamma ((A : ℂ)+3/2-I*z)/(Real.pi : ℂ)

/-- The analytic representative used on the wider contour. -/
def spectralABLExceptionalWideCorrected (a : ℝ) (A : ℕ) (z : ℂ) : ℂ :=
  (2*Complex.cos (2*z*(Real.log a : ℂ)))^2/(z^2+(2*(A : ℂ))^2)^(2*A)*
    spectralABLExceptionalWideGamma A z

theorem spectralABLExceptionalWideGamma_recurrence (A : ℕ) (z : ℂ)
    (hz : |z.im| < 3/2) :
    Complex.Gamma ((A : ℂ)+3/2+I*z)*Complex.Gamma ((A : ℂ)+3/2-I*z) =
      (Complex.Gamma (3/2+I*z)*Complex.Gamma (3/2-I*z))*
        ∏ k ∈ Finset.range A, (z^2+(((2*(k+1)+1 : ℕ) : ℂ)/2)^2) := by
  induction A with
  | zero => simp
  | succ A ih =>
    let p : ℂ := (A : ℂ)+3/2+I*z
    let m : ℂ := (A : ℂ)+3/2-I*z
    have hp : 0 < p.re := by
      dsimp [p]
      norm_num [Complex.mul_re]
      linarith [(abs_lt.mp hz).2, Nat.cast_nonneg (α:=ℝ) A]
    have hm : 0 < m.re := by
      dsimp [m]
      norm_num [Complex.mul_re]
      linarith [(abs_lt.mp hz).1, Nat.cast_nonneg (α:=ℝ) A]
    have hp0 : p ≠ 0 := by
      intro hp0
      rw [hp0,Complex.zero_re] at hp
      exact (lt_irrefl _ hp)
    have hm0 : m ≠ 0 := by
      intro hm0
      rw [hm0,Complex.zero_re] at hm
      exact (lt_irrefl _ hm)
    have hfac : p*m = z^2+(((2*(A+1)+1 : ℕ) : ℂ)/2)^2 := by
      dsimp [p,m]
      push_cast
      ring_nf
      simp only [I_sq]
      ring
    rw [Nat.cast_succ,
      show (A : ℂ)+1+3/2+I*z = p+1 by dsimp [p];ring,
      show (A : ℂ)+1+3/2-I*z = m+1 by dsimp [m];ring,
      Complex.Gamma_add_one p hp0,Complex.Gamma_add_one m hm0,
      Finset.prod_range_succ]
    calc
      _ = (Complex.Gamma p*Complex.Gamma m)*(p*m) := by ring
      _ = _ := by
        rw [hfac]
        dsimp only [p,m]
        rw [ih]
        ring

theorem spectralABLExceptionalWideCorrected_eq (a : ℝ) (A : ℕ) (z : ℂ)
    (hz : |z.im| < 3/2) :
    spectralABLExceptionalWideCorrected a A z = spectralABLExceptionalCorrected a A z := by
  rw [spectralABLExceptionalWideCorrected,spectralABLExceptionalWideGamma,
    spectralABLExceptionalWideGamma_recurrence A z hz]
  unfold spectralABLExceptionalCorrected spectralABLExceptionalBase spectralABLCoshCancellation
  ring

theorem spectralABLExceptionalWideCorrected_real (a : ℝ) (A : ℕ) (t : ℝ) :
    spectralABLExceptionalWideCorrected a A (t : ℂ) = spectralABLExceptionalCorrected a A (t : ℂ) :=
  spectralABLExceptionalWideCorrected_eq a A _ (by norm_num)

theorem spectralABLExceptionalWideCorrected_differentiableAt (a : ℝ) {A : ℕ}
    (hA : 1 ≤ A) (z : ℂ) (hz : |z.im| ≤ (A : ℝ)) :
    DifferentiableAt ℂ (spectralABLExceptionalWideCorrected a A) z := by
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hp : 0 < ((A : ℂ)+3/2+I*z).re := by
    norm_num [Complex.mul_re]
    linarith [(abs_le.mp hz).2]
  have hm : 0 < ((A : ℂ)+3/2-I*z).re := by
    norm_num [Complex.mul_re]
    linarith [(abs_le.mp hz).1]
  have hgp := (Complex.hasDerivAt_Gamma_of_re_pos hp).differentiableAt.comp z
    (show DifferentiableAt ℂ (fun w : ℂ => (A : ℂ)+3/2+I*w) z from by fun_prop)
  have hgm := (Complex.hasDerivAt_Gamma_of_re_pos hm).differentiableAt.comp z
    (show DifferentiableAt ℂ (fun w : ℂ => (A : ℂ)+3/2-I*w) z from by fun_prop)
  have hd := spectralABLExceptionalWindow_den_ne_zero A z (by linarith)
  unfold spectralABLExceptionalWideCorrected spectralABLExceptionalWideGamma
  apply DifferentiableAt.mul
  · apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero _ hd
  · exact (hgp.mul hgm).div_const _

end
end ArtinMatthews
