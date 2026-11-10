module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ArtinMatthews.SpectralGammaHalfDecay
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Complex
noncomputable section

theorem spectralGamma_half_integer_shift_norm_le (N k : ℕ) (hk : k ≤ N) (t : ℝ) :
    ‖Complex.Gamma ((k : ℂ)+1/2+(t : ℂ)*I)‖ ≤
      (((N : ℝ)+1)*(1+|t|))^k * ‖Complex.Gamma (1/2+(t : ℂ)*I)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    let z : ℂ := (k : ℂ)+1/2+(t : ℂ)*I
    let D : ℝ := ((N : ℝ)+1)*(1+|t|)
    have hz : z ≠ 0 := by
      intro hz
      have h := congrArg Complex.re hz
      norm_num [z,Complex.mul_re] at h
      linarith [Nat.cast_nonneg (α:=ℝ) k]
    have hcast : (k : ℂ)+1/2 = (((k : ℝ)+1/2 : ℝ) : ℂ) := by push_cast; rfl
    have hn : ‖z‖ ≤ D := by
      have hk' : (k : ℝ) ≤ N := by exact_mod_cast (show k ≤ N by omega)
      calc
        _ ≤ ‖(k : ℂ)+1/2‖+‖(t : ℂ)*I‖ := norm_add_le _ _
        _ = (k : ℝ)+1/2+|t| := by
          rw [hcast,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ (k : ℝ)+1/2)]
          simp
        _ ≤ _ := by
          dsimp [D]
          nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (abs_nonneg t)]
    rw [show ((k+1 : ℕ) : ℂ)+1/2+(t : ℂ)*I = z+1 by
      dsimp [z]; push_cast; ring,Complex.Gamma_add_one z hz,norm_mul]
    calc
      _ ≤ D*(D^k*‖Complex.Gamma (1/2+(t : ℂ)*I)‖) :=
        mul_le_mul hn (ih (by omega)) (norm_nonneg _) (by dsimp [D]; positivity)
      _ = _ := by rw [pow_succ]; ring

theorem spectralGamma_half_integer_pair_exp_bound (N m n k : ℕ)
    (hm : m ≤ N) (hn : n ≤ N) (hs : m+n = 2*k) (t : ℝ) :
    Real.exp (Real.pi*|t|)*
        ‖Complex.Gamma ((m : ℂ)+1/2+(t : ℂ)*I)*
          Complex.Gamma ((n : ℂ)+1/2+((-t : ℝ) : ℂ)*I)/(Real.pi : ℂ)‖ ≤
      2*(2*((N : ℝ)+1)^2)^k*(1+t^2)^k := by
  let D : ℝ := ((N : ℝ)+1)*(1+|t|)
  let G := ‖Complex.Gamma (1/2+(t : ℂ)*I)‖
  have hneg : ‖Complex.Gamma (1/2+((-t : ℝ) : ℂ)*I)‖ = G := by
    simpa only [G,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      spectralGamma_vertical_norm_even (1/2) t
  have hp := spectralGamma_half_integer_shift_norm_le N m hm t
  have hq := spectralGamma_half_integer_shift_norm_le N n hn (-t)
  rw [abs_neg,hneg] at hq
  have hprod : ‖Complex.Gamma ((m : ℂ)+1/2+(t : ℂ)*I)‖*
      ‖Complex.Gamma ((n : ℂ)+1/2+((-t : ℝ) : ℂ)*I)‖ ≤ D^(2*k)*G^2 := by
    calc
      _ ≤ (D^m*G)*(D^n*G) := mul_le_mul hp hq (norm_nonneg _) (by dsimp [D,G]; positivity)
      _ = _ := by rw [← hs,pow_add];ring
  have hcosh : 0 < Real.cosh (Real.pi*t) := Real.cosh_pos _
  have hexp : Real.exp (Real.pi*|t|) ≤ 2*Real.cosh (Real.pi*t) := by
    rw [← Real.cosh_abs (Real.pi*t),abs_mul,abs_of_pos Real.pi_pos,Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi*|t|))]
  have hD : D^(2*k) ≤ (2*((N : ℝ)+1)^2)^k*(1+t^2)^k := by
    rw [pow_mul,← mul_pow]
    apply pow_le_pow_left₀ (sq_nonneg D)
    have hu : (1+|t|)^2 ≤ 2*(1+t^2) := by
      nlinarith [sq_abs t,sq_nonneg (|t|-1)]
    calc
      D^2 = ((N : ℝ)+1)^2*(1+|t|)^2 := mul_pow _ _ _
      _ ≤ ((N : ℝ)+1)^2*(2*(1+t^2)) := mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ = _ := by ring
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ (Real.exp (Real.pi*|t|)/Real.pi)*(D^(2*k)*G^2) := by
      rw [show ∀ u v : ℝ, Real.exp (Real.pi*|t|)*(u*v/Real.pi) =
          (Real.exp (Real.pi*|t|)/Real.pi)*(u*v) by intros; ring]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = D^(2*k)*(Real.exp (Real.pi*|t|)/Real.cosh (Real.pi*t)) := by
      rw [show G^2 = Real.pi/Real.cosh (Real.pi*t) from spectralGamma_half_norm_sq t]
      field_simp [Real.pi_ne_zero,hcosh.ne']
    _ ≤ D^(2*k)*2 := mul_le_mul_of_nonneg_left ((div_le_iff₀ hcosh).mpr (by linarith))
      (by dsimp [D]; positivity)
    _ ≤ _ := by
      rw [mul_comm (D^(2*k)) 2, mul_assoc]
      exact mul_le_mul_of_nonneg_left hD (by norm_num)

end
end ArtinMatthews
