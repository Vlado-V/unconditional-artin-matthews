module

public import ArtinMatthews.SpectralPeterssonPeriodizedTaylor
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Tactic.NormNum.Parity


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine q-expansion of the holomorphic periodized Weyl profile.
The factorial-weighted double series is absolutely summable. -/

noncomputable section
open UpperHalfPlane

namespace ArtinMatthews

def spectralPeterssonLipschitzTerm (k : ℕ) (α : ℂ) (j : ℕ) (n : ℕ+) : ℂ :=
  α^j/(j.factorial : ℂ)*
    ((-2*(Real.pi : ℂ)*Complex.I)^(k+j)/((k+j-1).factorial : ℂ))*(n : ℂ)^(k+j-1)

def spectralPeterssonPeriodizedCoefficient (k : ℕ) (α : ℂ) (n : ℕ+) : ℂ :=
  ∑' j, spectralPeterssonLipschitzTerm k α j n

private theorem spectralPeterssonLipschitzTerm_norm (k : ℕ) (hk : 2 ≤ k)
    (α : ℂ) (z : UpperHalfPlane) (j : ℕ) (n : ℕ+) :
    let v := Real.pi*z.im
    let w := 2*Real.pi
    ‖spectralPeterssonLipschitzTerm k α j n*
      Complex.exp (2*(Real.pi : ℂ)*Complex.I*(z : ℂ))^(n : ℕ)‖ ≤
      ((‖α‖*w/v)^j/(j.factorial : ℝ))*
        (w^k*(n : ℝ)^(k-1)*Real.exp (-v*(n : ℝ))) := by
  dsimp only
  let v := Real.pi*z.im
  let w := 2*Real.pi
  let t : ℝ := (n : ℕ)
  have hv : 0 < v := mul_pos Real.pi_pos z.im_pos
  have hw : 0 < w := mul_pos two_pos Real.pi_pos
  have ht : 0 < t := Nat.cast_pos.mpr n.property
  have hpow : k+j-1 = k-1+j := by omega
  have hq : ‖Complex.exp (2*(Real.pi : ℂ)*Complex.I*(z : ℂ))‖ = Real.exp (-2*v) := by
    rw [Complex.norm_exp]
    congr 1
    simp [v,Complex.mul_re,Complex.mul_im]
    ring
  have hwC : ‖-2*(Real.pi : ℂ)*Complex.I‖ = w := by
    dsimp only [w]
    rw [norm_mul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  have hft : (j.factorial : ℝ) ≤ ((k+j-1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show j ≤ k+j-1 by omega)
  have hbr : (v*t)^j/((k+j-1).factorial : ℝ)*Real.exp (-v*t) ≤ 1 := by
    have h₁ : (v*t)^j/((k+j-1).factorial : ℝ) ≤ Real.exp (v*t) :=
      (div_le_div_of_nonneg_left (pow_nonneg (mul_nonneg hv.le ht.le) _)
        (Nat.cast_pos.mpr (Nat.factorial_pos _)) hft).trans
        (Real.pow_div_factorial_le_exp (v*t) (mul_nonneg hv.le ht.le) j)
    calc
      _ ≤ Real.exp (v*t)*Real.exp (-v*t) := mul_le_mul_of_nonneg_right h₁ (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add,show v*t+-v*t=0 by ring,Real.exp_zero]
  have hqpow : (Real.exp (-2*v))^(n : ℕ) = Real.exp (-v*t)*Real.exp (-v*t) := by
    rw [← Real.exp_nat_mul,← Real.exp_add]
    congr 1
    dsimp only [t]
    ring
  unfold spectralPeterssonLipschitzTerm
  rw [norm_mul,norm_mul,norm_mul,norm_div,norm_div,norm_pow,norm_pow,norm_pow,norm_pow,
    Complex.norm_natCast,Complex.norm_natCast,Complex.norm_natCast,hwC,hq,hqpow]
  change ‖α‖^j/(j.factorial : ℝ)*
      (w^(k+j)/((k+j-1).factorial : ℝ))*t^(k+j-1)*
      (Real.exp (-v*t)*Real.exp (-v*t)) ≤
    ((‖α‖*w/v)^j/(j.factorial : ℝ))*(w^k*t^(k-1)*Real.exp (-v*t))
  calc
    _ = ((‖α‖*w/v)^j/(j.factorial : ℝ))*(w^k*t^(k-1)*Real.exp (-v*t))*
        ((v*t)^j/((k+j-1).factorial : ℝ)*Real.exp (-v*t)) := by
      rw [show t^(k+j-1) = t^(k-1)*t^j by rw [hpow,pow_add],pow_add,div_pow,mul_pow,mul_pow]
      field_simp [hv.ne',Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j),
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k+j-1))]
      dsimp only [w]
      simp only [mul_pow]
      ring
    _ ≤ _ := by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hbr (by positivity :
        0 ≤ ((‖α‖*w/v)^j/(j.factorial : ℝ))*(w^k*t^(k-1)*Real.exp (-v*t))))

theorem spectralPeterssonPeriodizedExponential_qExpansion (k : ℕ) (hk : 2 ≤ k)
    (α : ℂ) (z : UpperHalfPlane) :
    let q := Complex.exp (2*(Real.pi : ℂ)*Complex.I*(z : ℂ))
    Summable (fun n : ℕ+ => spectralPeterssonPeriodizedCoefficient k α n*q^(n : ℕ)) ∧
      spectralPeterssonPeriodizedExponential k α z =
        ∑' n : ℕ+, spectralPeterssonPeriodizedCoefficient k α n*q^(n : ℕ) := by
  let q := Complex.exp (2*(Real.pi : ℂ)*Complex.I*(z : ℂ))
  let v := Real.pi*z.im
  let w := 2*Real.pi
  let f (j : ℕ) (n : ℕ+) : ℂ := spectralPeterssonLipschitzTerm k α j n*q^(n : ℕ)
  let b (j : ℕ) : ℝ := (‖α‖*w/v)^j/(j.factorial : ℝ)
  let a (n : ℕ+) : ℝ := w^k*(n : ℝ)^(k-1)*Real.exp (-v*(n : ℝ))
  have hv : 0 < v := mul_pos Real.pi_pos z.im_pos
  have ha : Summable a := by
    have hp := (Real.summable_pow_mul_exp_neg_nat_mul (k-1) hv).comp_injective
      (show Function.Injective (fun n : ℕ+ => (n : ℕ)) from Subtype.val_injective)
    simpa only [a,Function.comp_def,mul_assoc,neg_mul] using hp.mul_left (w^k)
  have hb : Summable b := Real.summable_pow_div_factorial _
  have hp : Summable (fun p : ℕ × ℕ+ => b p.1*a p.2) :=
    Summable.mul_of_nonneg hb ha (fun j => by dsimp only [b,v,w]; positivity)
      (fun n => by dsimp only [a,w]; positivity)
  have hnorm : Summable (fun p : ℕ × ℕ+ => ‖f p.1 p.2‖) :=
    Summable.of_nonneg_of_le (g := fun p : ℕ × ℕ+ => ‖f p.1 p.2‖)
      (f := fun p : ℕ × ℕ+ => b p.1*a p.2) (fun _ => norm_nonneg _)
      (fun p => spectralPeterssonLipschitzTerm_norm k hk α z p.1 p.2) hp
  have hf : Summable (Function.uncurry f) := hnorm.of_norm
  have hterm (n : ℕ+) : (∑' j, f j n) =
      spectralPeterssonPeriodizedCoefficient k α n*q^(n : ℕ) := tsum_mul_right
  refine ⟨hf.prod_symm.prod.congr hterm, ?_⟩
  calc
    _ = ∑' j : ℕ, ∑' n : ℕ+, f j n := by
      rw [spectralPeterssonPeriodizedExponential_lipschitz k hk α z]
      apply tsum_congr
      intro j
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      unfold f spectralPeterssonLipschitzTerm q
      ring
    _ = ∑' n : ℕ+, ∑' j : ℕ, f j n := hf.tsum_comm.symm
    _ = _ := tsum_congr hterm

end ArtinMatthews
