module

public import ArtinMatthews.ShiftedABLSourceBudget
public import Mathlib.Analysis.Real.Pi.Bounds
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The exact radial scale of one nonempty signed source block, compared
with the literal ABL conductor and its Bessel scale. -/

noncomputable section
namespace ArtinMatthews

theorem shiftedABLRadialParameter_bounds
    {F L n r : ℕ} {ρ : ℤ} {R Z : ℝ}
    (hF : 0 < F) (hL : 0 < L) (hn : 0 < n) (hr : 0 < r)
    (hR : 1 ≤ R) (hρ : R ≤ (ρ.natAbs : ℝ)) (hZ : 1 ≤ Z) :
    let P' := ablTheorem24SpectralParameter (3*(L : ℝ)/(F : ℝ)) R Z n r F
    let a := 4*Real.pi*Real.sqrt ((ρ.natAbs : ℝ)*(n : ℝ)) /
      (Real.sqrt (r : ℝ)*(3*(L : ℝ)))
    let X := ablTheorem24BesselScale (3*(L : ℝ)/(F : ℝ)) R n r F
    P' = (3*(L : ℝ))*R*Z*n*r ∧ 1 ≤ P' ∧
      0 < X ∧ X ≤ a ∧ (P')⁻¹ ≤ a := by
  intro P' a X
  have hF0 : (F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hF.ne'
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hρ1 : (1 : ℝ) ≤ ρ.natAbs := hR.trans hρ
  have hL0 : (0 : ℝ) < L := zero_lt_one.trans_le hL1
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans_le hr1
  have hsqr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hr0
  have hden : 0 < Real.sqrt (r : ℝ)*(3*(L : ℝ)) := by positivity
  have hπ : (1 : ℝ) ≤ 4*Real.pi := by linarith [Real.pi_gt_three]
  have hPeq : P' = (3*(L : ℝ))*R*Z*n*r := by
    dsimp [P',ablTheorem24SpectralParameter]
    field_simp [hF0]
  have hP1 : 1 ≤ P' := by
    rw [hPeq]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (by linarith : (1 : ℝ) ≤ 3*L) hR) hZ) hn1) hr1
  have hP0 : 0 < P' := zero_lt_one.trans_le hP1
  have hXeq : X = Real.sqrt (R*(n : ℝ))/(Real.sqrt (r : ℝ)*(3*(L : ℝ))) := by
    dsimp [X,ablTheorem24BesselScale]
    congr 1
    field_simp [hF0]
  have hX : 0 < X := by
    rw [hXeq]
    exact div_pos (Real.sqrt_pos.2 (mul_pos (zero_lt_one.trans_le hR) hn0)) hden
  have hXle : X ≤ a := by
    rw [hXeq]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      _ ≤ Real.sqrt ((ρ.natAbs : ℝ)*(n : ℝ)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hρ hn0.le)
      _ ≤ 4*Real.pi*Real.sqrt ((ρ.natAbs : ℝ)*(n : ℝ)) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hπ (Real.sqrt_nonneg _)
  have hsqrLe : Real.sqrt (r : ℝ) ≤ r :=
    Real.sqrt_le_iff.2 ⟨hr0.le, by nlinarith⟩
  have hnum : 1 ≤ 4*Real.pi*Real.sqrt ((ρ.natAbs : ℝ)*(n : ℝ)) :=
    one_le_mul_of_one_le_of_one_le hπ
      (Real.one_le_sqrt.2 (one_le_mul_of_one_le_of_one_le hρ1 hn1))
  have hdenP : Real.sqrt (r : ℝ)*(3*(L : ℝ)) ≤ P' := by
    calc
      _ ≤ (r : ℝ)*(3*(L : ℝ)) :=
        mul_le_mul_of_nonneg_right hsqrLe (by positivity)
      _ ≤ ((r : ℝ)*(3*(L : ℝ)))*(R*Z*(n : ℝ)) := by
        exact le_mul_of_one_le_right (by positivity)
          (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hR hZ) hn1)
      _ = P' := by rw [hPeq]; ring
  have hinv : P'⁻¹ ≤ a := by
    rw [← one_div]
    change 1/P' ≤ 4*Real.pi*Real.sqrt ((ρ.natAbs : ℝ)*(n : ℝ)) /
      (Real.sqrt (r : ℝ)*(3*(L : ℝ)))
    apply (div_le_div_iff₀ hP0 hden).2
    calc
      _ = Real.sqrt (r : ℝ)*(3*(L : ℝ)) := by ring
      _ ≤ P' := hdenP
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnum hP0.le
  exact ⟨hPeq,hP1,hX,hXle,hinv⟩

end ArtinMatthews
