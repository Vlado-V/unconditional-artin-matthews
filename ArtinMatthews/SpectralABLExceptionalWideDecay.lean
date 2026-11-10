module

public import ArtinMatthews.SpectralABLExceptionalWideWindow
public import ArtinMatthews.SpectralABLExceptionalStrip
public import ArtinMatthews.SpectralABLExceptionalWideGammaBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Complex
noncomputable section

theorem spectralABLExceptionalWide_den_norm_lower {A : ℕ} (hA : 1 ≤ A)
    (t y : ℝ) (hy : |y| ≤ (A : ℝ)) :
    1+t^2 ≤ ‖((t : ℂ)+(y : ℂ)*I)^2+(2*(A : ℂ))^2‖ := by
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hy2 : y^2 ≤ (A : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) (Nat.cast_nonneg A)).mpr hy
  have hA2 : (1 : ℝ) ≤ (A : ℝ)^2 := one_le_pow₀ hA'
  have hre : (((t : ℂ)+(y : ℂ)*I)^2+(2*(A : ℂ))^2).re = t^2-y^2+4*(A : ℝ)^2 := by
    norm_num [pow_two,Complex.mul_re,Complex.mul_im]
    ring
  have hlower : 1+t^2 ≤ (((t : ℂ)+(y : ℂ)*I)^2+(2*(A : ℂ))^2).re := by
    rw [hre]
    linarith
  exact hlower.trans (Complex.re_le_norm _)

theorem spectralABLExceptionalWide_phase_bound (a t y : ℝ) :
    ‖(2*Complex.cos (2*((t : ℂ)+(y : ℂ)*I)*(Real.log a : ℂ)))^2‖ ≤
      4*Real.exp (4 * |y| * |Real.log a|) := by
  let z : ℂ := 2*((t : ℂ)+(y : ℂ)*I)*(Real.log a : ℂ)
  have him : z.im = 2*y*Real.log a := by
    norm_num [z,Complex.mul_re,Complex.mul_im]
  have hc : ‖Complex.cos z‖ ≤ Real.exp (2 * |y| * |Real.log a|) := by
    simpa only [him,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] using
      spectral_norm_cos_le_exp_abs_im z
  change ‖(2*Complex.cos z)^2‖ ≤ _
  rw [norm_pow,norm_mul,show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  calc
    _ ≤ (2*Real.exp (2 * |y| * |Real.log a|))^2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hc (by norm_num)) 2
    _ = 4*(Real.exp (2 * |y| * |Real.log a|)*Real.exp (2 * |y| * |Real.log a|)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem spectralABLExceptionalWideCorrected_exp_bound_at (A : ℕ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a t : ℝ) (y : ℕ), y ≤ A →
      Real.exp (Real.pi*|t|)*‖spectralABLExceptionalWideCorrected a A ((t : ℂ)+(y : ℂ)*I)‖ ≤
        C*Real.exp (4*(y : ℝ)*|Real.log a|)/(1+t^2)^(A-1) := by
  let D := 2*(2*(((2*A+1 : ℕ) : ℝ)+1)^2)^(A+1)
  refine ⟨4*D,by dsimp [D];positivity,?_⟩
  intro a t y hy
  let z : ℂ := (t : ℂ)+(y : ℂ)*I
  let P := (2*Complex.cos (2*z*(Real.log a : ℂ)))^2
  let Q := z^2+(2*(A : ℂ))^2
  let u := 1+t^2
  let E := Real.exp (4*(y : ℝ)*|Real.log a|)
  have hu : 0 < u := by dsimp [u];positivity
  have hyabs : |(y : ℝ)| ≤ (A : ℝ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) y)]
    exact_mod_cast hy
  have hd : u ≤ ‖Q‖ := by
    simpa only [z,Q,u,Complex.ofReal_natCast] using
      spectralABLExceptionalWide_den_norm_lower hA t (y : ℝ) hyabs
  have hp : ‖P‖ ≤ 4*E := by
    simpa only [z,P,E,Complex.ofReal_natCast,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) y)] using
      spectralABLExceptionalWide_phase_bound a t (y : ℝ)
  have hg : Real.exp (Real.pi*|t|)*‖spectralABLExceptionalWideGamma A z‖ ≤ D*u^(A+1) :=
    spectralABLExceptionalWideGamma_exp_bound_at A y hy t
  have hq : ‖P‖/‖Q‖^(2*A) ≤ 4*E/u^(2*A) :=
    (div_le_div_of_nonneg_left (norm_nonneg P) (pow_pos hu _)
      (pow_le_pow_left₀ hu.le hd _)).trans
      (div_le_div_of_nonneg_right hp (pow_nonneg hu.le _))
  change Real.exp (Real.pi*|t|)*‖P/Q^(2*A)*spectralABLExceptionalWideGamma A z‖ ≤ _
  rw [norm_mul,norm_div,show ‖Q^(2*A)‖ = ‖Q‖^(2*A) from norm_pow _ _]
  calc
    _ = (‖P‖/‖Q‖^(2*A))*(Real.exp (Real.pi*|t|)*‖spectralABLExceptionalWideGamma A z‖) := by ring
    _ ≤ (4*E/u^(2*A))*(D*u^(A+1)) := mul_le_mul hq hg (by positivity) (by positivity)
    _ = _ := by
      change (4*E/u^(2*A))*(D*u^(A+1)) = (4*D)*E/u^(A-1)
      rw [show 2*A = A+1+(A-1) by omega,pow_add]
      field_simp [hu.ne']

theorem spectralABLExceptionalWideCorrected_strip_bound (a : ℝ) {A : ℕ} (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t y : ℝ, |y| ≤ (A : ℝ) →
      ‖spectralABLExceptionalWideCorrected a A ((t : ℂ)+(y : ℂ)*I)‖ ≤ C := by
  obtain ⟨G,hG,hGamma⟩ := spectralABLExceptionalWideGamma_strip_bound A
  let E := Real.exp (4*(A : ℝ)*|Real.log a|)
  refine ⟨4*E*G,by dsimp [E];positivity,?_⟩
  intro t y hy
  let z : ℂ := (t : ℂ)+(y : ℂ)*I
  let P := (2*Complex.cos (2*z*(Real.log a : ℂ)))^2
  let Q := z^2+(2*(A : ℂ))^2
  have hd : 1+t^2 ≤ ‖Q‖ := spectralABLExceptionalWide_den_norm_lower hA t y hy
  have hp : ‖P‖ ≤ 4*E := by
    apply (spectralABLExceptionalWide_phase_bound a t y).trans
    dsimp [E]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy (by norm_num)) (abs_nonneg _)
  have hq : ‖P‖/‖Q‖^(2*A) ≤ 4*E :=
    (div_le_self (norm_nonneg P) (one_le_pow₀ (by linarith [sq_nonneg t]))).trans hp
  have hg : ‖spectralABLExceptionalWideGamma A z‖ ≤ G := hGamma z (by simpa [z] using hy)
  change ‖P/Q^(2*A)*spectralABLExceptionalWideGamma A z‖ ≤ _
  rw [norm_mul,norm_div,show ‖Q^(2*A)‖ = ‖Q‖^(2*A) from norm_pow _ _]
  exact mul_le_mul hq hg (norm_nonneg _) (by positivity)

end
end ArtinMatthews
