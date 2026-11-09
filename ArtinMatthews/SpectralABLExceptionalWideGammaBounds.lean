module

public import ArtinMatthews.SpectralABLExceptionalWideWindow
public import ArtinMatthews.SpectralGammaHalfIntegerGrowth


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex
noncomputable section

theorem spectralABLExceptionalWideGamma_exp_bound_at (A y : ℕ) (hy : y ≤ A) (t : ℝ) :
    Real.exp (Real.pi*|t|)*‖spectralABLExceptionalWideGamma A ((t : ℂ)+(y : ℂ)*I)‖ ≤
      2*(2*(((2*A+1 : ℕ) : ℝ)+1)^2)^(A+1)*(1+t^2)^(A+1) := by
  have hy' : y ≤ A+1 := by omega
  have hp : (A : ℂ)+3/2+I*((t : ℂ)+(y : ℂ)*I) =
      ((A+1-y : ℕ) : ℂ)+1/2+(t : ℂ)*I := by
    rw [Nat.cast_sub hy']
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  have hm : (A : ℂ)+3/2-I*((t : ℂ)+(y : ℂ)*I) =
      ((A+1+y : ℕ) : ℂ)+1/2+((-t : ℝ) : ℂ)*I := by
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  rw [spectralABLExceptionalWideGamma,hp,hm]
  exact spectralGamma_half_integer_pair_exp_bound (2*A+1) (A+1-y) (A+1+y) (A+1)
    (by omega) (by omega) (by omega) t

theorem spectralABLExceptionalWideGamma_strip_bound (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, |z.im| ≤ (A : ℝ) →
      ‖spectralABLExceptionalWideGamma A z‖ ≤ C := by
  let upper : ℝ := 2*(A : ℝ)+3/2
  have hg : ContinuousOn Real.Gamma (Ioi (0 : ℝ)) := by
    intro x hx
    change 0 < x at hx
    exact (Real.differentiableAt_Gamma (fun n => by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)).continuousAt.continuousWithinAt
  have hc : ContinuousOn Real.Gamma (Icc (3/2) upper) :=
    hg.mono (fun x hx => by change 0 < x; linarith [hx.1])
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hl : (3/2 : ℝ) ≤ upper := by dsimp [upper]; linarith [Nat.cast_nonneg (α:=ℝ) A]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (3/2) ⟨le_rfl,hl⟩)
  refine ⟨(M+1)^2/Real.pi,by positivity,?_⟩
  intro z hz
  have hp : ((A : ℂ)+3/2+I*z).re ∈ Icc (3/2) upper := by
    norm_num [upper,Complex.mul_re]
    constructor <;> linarith [(abs_le.mp hz).1,(abs_le.mp hz).2]
  have hm : ((A : ℂ)+3/2-I*z).re ∈ Icc (3/2) upper := by
    norm_num [upper,Complex.mul_re]
    constructor <;> linarith [(abs_le.mp hz).1,(abs_le.mp hz).2]
  have hb (w : ℂ) (hw : w.re ∈ Icc (3/2) upper) : ‖Complex.Gamma w‖ ≤ M+1 := by
    have hr : 0 < w.re := by linarith [hw.1]
    have hreal : Real.Gamma w.re ≤ M := (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hM w.re hw)
    exact (spectralGamma_norm_le_real w hr).trans (hreal.trans (by linarith))
  rw [spectralABLExceptionalWideGamma,norm_div,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le,pow_two]
  exact div_le_div_of_nonneg_right (mul_le_mul (hb _ hp) (hb _ hm) (norm_nonneg _) (by linarith))
    Real.pi_pos.le

end
end ArtinMatthews
