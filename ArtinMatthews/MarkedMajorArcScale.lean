module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

/-! Numerical passage from the proved weak VK strip to a common rectangle.
The two logarithmic height and conductor weights are absorbed uniformly,
without restricting the fixed exponent in the polylogarithmic modulus. -/
namespace ArtinMatthews

open Filter
open scoped Topology

/-- A uniform numerical rectangle budget. `H` is the logarithmic height and
`W` the logarithmic conductor/height weight. -/
theorem marked_major_arc_rectangle_budget (A b c : ℝ)
    (hA : 1 ≤ A) (hb : 1 ≤ b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ H W : ℝ,
      0 < H → H ≤ b * L → 0 < W → W ≤ A * Real.log L →
      L ^ (-(3 / 4 : ℝ)) ≤ c * H ^ (-(2 / 3 : ℝ)) / W ∧
      W ^ 2 * H ^ (2 / 3 : ℝ) ≤ L ^ 2 ∧
      1 / L ≤ H ^ (-(2 / 3 : ℝ)) / 16 := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hbp : 0 < b := zero_lt_one.trans_le hb
  let ε := min (c / (A*b)) (1 / (A*b))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/12)).bound hε
  have hlim : Tendsto (fun L : ℝ => 16*b*L^(-(1/3:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).const_mul (16*b)
  filter_upwards [hlog, hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    eventually_ge_atTop (1:ℝ)] with L hlog hlarge hL
  intro H W hH hHup hW hWup
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL0 _)] at hlog
  have hpow : H ^ (2/3:ℝ) ≤ b * L ^ (2/3:ℝ) := by
    apply (Real.rpow_le_rpow hH.le hHup (by norm_num : (0:ℝ)≤2/3)).trans
    rw [Real.mul_rpow hbp.le hL0.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL0.le _)
    exact Real.rpow_le_self_of_one_le hb (by norm_num)
  have hWc : W ≤ (c/b) * L^(1/12:ℝ) := by
    calc
      W ≤ A*Real.log L := hWup
      _ ≤ A*(ε*L^(1/12:ℝ)) := mul_le_mul_of_nonneg_left hlog hAp.le
      _ ≤ A*((c/(A*b))*L^(1/12:ℝ)) := by gcongr; exact min_le_left _ _
      _ = _ := by field_simp
  have hW1 : W ≤ (1/b) * L^(1/12:ℝ) := by
    calc
      W ≤ A*Real.log L := hWup
      _ ≤ A*(ε*L^(1/12:ℝ)) := mul_le_mul_of_nonneg_left hlog hAp.le
      _ ≤ A*((1/(A*b))*L^(1/12:ℝ)) := by gcongr; exact min_le_right _ _
      _ = _ := by field_simp
  have hid : L^(-(3/4:ℝ)) * L^(1/12:ℝ) * L^(2/3:ℝ) = 1 := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · apply (le_div_iff₀ hW).mpr
    rw [Real.rpow_neg hH.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hH _)).mpr
    calc
      _ ≤ (L^(-(3/4:ℝ)) * ((c/b)*L^(1/12:ℝ))) * (b*L^(2/3:ℝ)) := by
        gcongr
      _ = c * (L^(-(3/4:ℝ)) * L^(1/12:ℝ) * L^(2/3:ℝ)) := by field_simp
      _ = c := by rw [hid, mul_one]
  · have hid2 : (L^(1/12:ℝ))^2 * L^(2/3:ℝ) = L^(5/6:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
      norm_num
    calc
      _ ≤ ((1/b)*L^(1/12:ℝ))^2 * (b*L^(2/3:ℝ)) := by gcongr
      _ = (1/b) * ((L^(1/12:ℝ))^2 * L^(2/3:ℝ)) := by field_simp
      _ = (1/b) * L^(5/6:ℝ) := by rw [hid2]
      _ ≤ 1 * L^(5/6:ℝ) := by gcongr; exact (div_le_one hbp).mpr hb
      _ ≤ L^2 := by
        rw [one_mul, ← Real.rpow_two]
        exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  · rw [Real.rpow_neg hH.le, ← one_div]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hH _)).mpr
    have hid3 : (16/L) * (b*L^(2/3:ℝ)) = 16*b*L^(-(1/3:ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one L]
      calc
        _ = (16*b) * (L^(-1:ℝ)*L^(2/3:ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hL0]; norm_num
    calc
      _ = (16/L) * H^(2/3:ℝ) := by ring
      _ ≤ (16/L) * (b*L^(2/3:ℝ)) := by gcongr
      _ ≤ 1 := by rw [hid3]; exact hlarge.le

end ArtinMatthews
