module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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

/-! The actual retained source ranges imply the fixed Bessel-scale and
auxiliary overlap conditions in the signed spectral estimate. -/

noncomputable section
namespace ArtinMatthews

theorem shiftedABL_source_bessel_square_bound {H B Q r n R W : ℝ}
    (hH : 0 < H) (hB : 0 < B) (hQ : 0 < Q) (hr : 0 < r)
    (hn : 0 ≤ n) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hRup : R ≤ 64*B*W*Q^2/H) (hrlow : B^2 ≤ r) (hnup : n ≤ 2*B) :
    (Real.sqrt (R*n)/(Real.sqrt r*Q))^2 ≤ 128*W/H := by
  have hprod : R*n ≤ 128*r*W*Q^2/H := by
    calc
      R*n ≤ (64*B*W*Q^2/H)*(2*B) := mul_le_mul hRup hnup hn (by positivity)
      _ = 128*B^2*W*Q^2/H := by ring
      _ ≤ _ := by gcongr
  have hx : (Real.sqrt (R*n)/(Real.sqrt r*Q))^2 = (R*n)/(r*Q^2) := by
    simp only [div_pow,mul_pow,Real.sq_sqrt (mul_nonneg hR hn),Real.sq_sqrt hr.le]
  rw [hx]
  apply (div_le_iff₀ (mul_pos hr (sq_pos_of_pos hQ))).mpr
  exact hprod.trans_eq (by ring)

theorem shiftedABL_source_bessel_conditions {H B Q r n R P N g ε : ℝ}
    (hH : 0 < H) (hB : 0 < B) (hQ : 0 < Q) (hr : 0 < r)
    (hn : 0 < n) (hR : 0 < R) (hP : 1 ≤ P) (hN : 1 ≤ N) (hg : 1 ≤ g)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hPdef : P=N*H)
    (hRup : R ≤ 64*B*P^ε*Q^2/H) (hrlow : B^2 ≤ r)
    (hnB : n ≤ 2*B) (hnH : n ≤ 2*H) :
    let X := Real.sqrt (R*n)/(Real.sqrt r*Q)
    let G := Real.sqrt (n*g)
    let V := 16*Real.sqrt (P^ε)
    0 < X ∧ X ≤ 16*N ∧ 1 ≤ V ∧ n*X ≤ V*G ∧ Real.sqrt V ≤ 4*P^ε := by
  intro X G V
  have hW : 1 ≤ P^ε := Real.one_le_rpow hP hε
  have hW0 : 0 ≤ P^ε := zero_le_one.trans hW
  have hWup : P^ε ≤ P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hε1
  have hX : 0 < X := by dsimp [X]; positivity
  have hXsq : X^2 ≤ 128*P^ε/H := shiftedABL_source_bessel_square_bound
    hH hB hQ hr hn.le hR.le hW0 hRup hrlow hnB
  have hXsqN : X^2 ≤ 128*N := by
    calc
      X^2 ≤ 128*P^ε/H := hXsq
      _ ≤ 128*P/H := by gcongr
      _ = 128*N := by rw [hPdef]; field_simp
  have hXup : X ≤ 16*N := by nlinarith [sq_nonneg N]
  have hV : 1 ≤ V := by
    have hs : 1 ≤ Real.sqrt (P^ε) := Real.one_le_sqrt.mpr hW
    dsimp [V]
    linarith
  have hVsq : V^2=256*P^ε := by dsimp [V]; rw [mul_pow,Real.sq_sqrt hW0]; norm_num
  have hGsq : G^2=n*g := by dsimp [G]; exact Real.sq_sqrt (by positivity)
  have hnXsq : (n*X)^2 ≤ 256*P^ε*n := by
    calc
      (n*X)^2 = n^2*X^2 := mul_pow _ _ _
      _ ≤ n^2*(128*P^ε/H) := mul_le_mul_of_nonneg_left hXsq (sq_nonneg n)
      _ = (128*P^ε*n)*(n/H) := by ring
      _ ≤ (128*P^ε*n)*2 := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ hH).mpr (by linarith)) (by positivity)
      _ = _ := by ring
  have hVG : n*X ≤ V*G := by
    apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) (by dsimp [G]; positivity)
    rw [mul_pow V G 2,hVsq,hGsq]
    exact hnXsq.trans (by nlinarith [mul_nonneg (show 0 ≤ 256*P^ε*n by positivity) (show 0 ≤ g-1 by linarith)])
  have hRootW : Real.sqrt (P^ε) ≤ P^ε := Real.sqrt_le_iff.mpr ⟨hW0,by nlinarith⟩
  have hRootV : Real.sqrt V ≤ 4*P^ε := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    dsimp [V]
    nlinarith
  exact ⟨hX,hXup,hV,hVG,hRootV⟩

end ArtinMatthews
