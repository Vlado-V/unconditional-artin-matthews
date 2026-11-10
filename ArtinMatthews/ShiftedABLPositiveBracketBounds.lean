module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! The two nondecaying source contributions have the exact arithmetic
weights required by the shifted correlation estimate. -/

noncomputable section
namespace ArtinMatthews

private theorem quarter_power_four {x : ℝ} (hx : 0 ≤ x) : (x^(1/4 : ℝ))^4=x := by
  rw [← Real.rpow_natCast (x^(1/4 : ℝ)) 4,← Real.rpow_mul hx]
  norm_num

private theorem three_quarters_power_four {x : ℝ} (hx : 0 ≤ x) :
    (x^(3/4 : ℝ))^4=x^3 := by
  rw [← Real.rpow_natCast (x^(3/4 : ℝ)) 4,← Real.rpow_mul hx]
  norm_num

private theorem sqrt_sqrt_power_four {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt (Real.sqrt x))^4=x := by
  rw [show (4 : ℕ)=2*2 by decide,pow_mul,
    Real.sq_sqrt (Real.sqrt_nonneg x),Real.sq_sqrt hx]

theorem shiftedABL_first_positive_bracket
    {H M N D d F R Q P ε : ℝ}
    (hH : 0 < H) (hM : 0 < M) (hN : 1 ≤ N) (hD : 0 ≤ D)
    (hd : 0 < d) (hR : 0 ≤ R) (hQ : 0 < Q) (hP : 1 ≤ P) (hε : 0 ≤ ε)
    (hF : F=N*D^2) (hRup : R ≤ 64*(M/d)*P^ε*Q^2/H) :
    H*Real.sqrt F*Real.sqrt R/Q ≤
      8*N*P^ε*(Real.sqrt (H+1)*Real.sqrt M*D/Real.sqrt d) := by
  let K := N*P^ε
  let Z := M*D^2/d
  have hK1 : 1 ≤ K := one_le_mul_of_one_le_of_one_le hN (Real.one_le_rpow hP hε)
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hKsq : K ≤ K^2 := by nlinarith
  have hprod : K*H ≤ K^2*(H+1) :=
    mul_le_mul hKsq (by linarith) hH.le (sq_nonneg K)
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (by positivity)
  calc
    (H*Real.sqrt F*Real.sqrt R/Q)^2 = H^2*F*R/Q^2 := by
      simp only [div_pow,mul_pow,Real.sq_sqrt hF0,Real.sq_sqrt hR]
    _ ≤ H^2*F*(64*(M/d)*P^ε*Q^2/H)/Q^2 := by gcongr
    _ = 64*(K*H)*Z := by
      rw [hF]
      dsimp [K,Z]
      field_simp
      <;> ring
    _ ≤ 64*(K^2*(H+1))*Z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num)) hZ
    _ = (8*N*P^ε*(Real.sqrt (H+1)*Real.sqrt M*D/Real.sqrt d))^2 := by
      simp only [mul_pow,div_pow,Real.sq_sqrt (show 0 ≤ H+1 by linarith),
        Real.sq_sqrt hM.le,Real.sq_sqrt hd.le]
      dsimp [K,Z]
      ring

theorem shiftedABL_second_positive_bracket
    {H M N D d r R Q P g ε : ℝ}
    (hH : 0 < H) (hM : 0 < M) (hN : 1 ≤ N) (hD : 0 < D)
    (hd : 0 < d) (hr : 0 < r) (hR : 0 ≤ R) (hQ : 0 < Q)
    (hP : 1 ≤ P) (hε : 0 ≤ ε) (hg : 0 ≤ g)
    (hRup : R ≤ 64*(M/d)*P^ε*Q^2/H) (hglow : g ≤ N*D/d)
    (hrlow : (M/d)^2 ≤ r) :
    H*Real.sqrt (Real.sqrt g)*Real.sqrt (Real.sqrt R)/
        (Real.sqrt Q*Real.sqrt (Real.sqrt r)) ≤
      4*N*P^ε*((H+1)^(3/4 : ℝ)*D^(1/4 : ℝ)/M^(1/4 : ℝ)) := by
  let K := N*P^ε
  have hK1 : 1 ≤ K := one_le_mul_of_one_le_of_one_le hN (Real.one_le_rpow hP hε)
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hK4 : K ≤ K^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK1 (show 1 ≤ (4 : ℕ) by decide)
  have h64 : 64*K ≤ 256*K^4 := by nlinarith [pow_nonneg hK0 4]
  have hH3 : H^3 ≤ (H+1)^3 := pow_le_pow_left₀ hH.le (by linarith) 3
  have hZ : 0 ≤ D/M := div_nonneg hD.le hM.le
  have hbound : (64*K)*H^3*(D/M) ≤ (256*K^4)*(H+1)^3*(D/M) :=
    mul_le_mul_of_nonneg_right (mul_le_mul h64 hH3 (pow_nonneg hH.le _) (by positivity)) hZ
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (by positivity)
  calc
    (H*Real.sqrt (Real.sqrt g)*Real.sqrt (Real.sqrt R)/
        (Real.sqrt Q*Real.sqrt (Real.sqrt r)))^4 = H^4*g*R/(Q^2*r) := by
      simp only [div_pow,mul_pow,sqrt_sqrt_power_four hg,sqrt_sqrt_power_four hR,
        sqrt_sqrt_power_four hr.le]
      rw [show (Real.sqrt Q)^4=((Real.sqrt Q)^2)^2 by ring,
        Real.sq_sqrt hQ.le]
    _ ≤ H^4*(N*D/d)*(64*(M/d)*P^ε*Q^2/H)/(Q^2*r) := by gcongr
    _ ≤ H^4*(N*D/d)*(64*(M/d)*P^ε*Q^2/H)/(Q^2*(M/d)^2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hrlow (sq_nonneg Q)
    _ = 64*K*H^3*(D/M) := by
      dsimp [K]
      field_simp
      <;> ring
    _ ≤ (256*K^4)*(H+1)^3*(D/M) := hbound
    _ = (4*N*P^ε*((H+1)^(3/4 : ℝ)*D^(1/4 : ℝ)/M^(1/4 : ℝ)))^4 := by
      simp only [mul_pow,div_pow,
        three_quarters_power_four (show 0 ≤ H+1 by linarith),
        quarter_power_four hD.le,quarter_power_four hM.le]
      dsimp [K]
      ring

end ArtinMatthews
