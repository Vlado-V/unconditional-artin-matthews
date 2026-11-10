module

public import ArtinMatthews.MarkedMajorFourierSeparationBase
public import Mathlib.RingTheory.Finiteness.Prod
public import ArtinMatthews.MarkedMajorFourierDecayRadial
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


set_option backward.privateInPublic true
@[expose] public section

/-! Simultaneous scaled coordinate decay for the actual Fourier coefficient
with its exact positive-exponential inversion normalization. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

def markedMajorFourierFrequency (p : ℝ × ℝ) : MarkedMajorFourierPlane :=
  markedMajorPlaneEquiv.symm (p.1/(2*Real.pi),p.2/(2*Real.pi))

theorem markedMajorFourierCoefficient_norm_le (g : SchwartzMap (ℝ × ℝ) ℂ) (p : ℝ × ℝ) :
    ‖markedMajorFourierCoefficient g p‖ ≤
      ‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ)
        (markedMajorFourierFrequency p)‖ := by
  have hc : 0 ≤ ((2*Real.pi)^2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hsq : 1 ≤ (2*Real.pi)^2 := by nlinarith [Real.two_le_pi]
  have hcle : |((2*Real.pi)^2)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg hc]
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hsq
  rw [markedMajorFourierCoefficient_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) hcle

theorem markedMajorFourierFrequency_coordinate_weights (N : ℕ) {W : ℝ} (hW : 1 ≤ W)
    (p : ℝ × ℝ) :
    (1+|p.1|/W)^N*(1+|p.2|/W)^N ≤
      (2*Real.pi)^(2*N)*(1+‖markedMajorFourierFrequency p‖/W)^(2*N) := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  have hpi : 0 < 2*Real.pi := by positivity
  have hpione : 1 ≤ 2*Real.pi := by nlinarith [Real.two_le_pi]
  have hx := WithLp.norm_fst_le (α := ℝ) (β := ℝ) (markedMajorFourierFrequency p)
  have hy := WithLp.norm_snd_le (α := ℝ) (β := ℝ) (markedMajorFourierFrequency p)
  change |p.1/(2*Real.pi)| ≤ ‖markedMajorFourierFrequency p‖ at hx
  change |p.2/(2*Real.pi)| ≤ ‖markedMajorFourierFrequency p‖ at hy
  rw [abs_div, abs_of_pos hpi] at hx hy
  have hx' := (div_le_iff₀ hpi).mp hx
  have hy' := (div_le_iff₀ hpi).mp hy
  have hxc : |p.1|/W ≤ (2*Real.pi)*(‖markedMajorFourierFrequency p‖/W) := by
    have h := div_le_div_of_nonneg_right hx' hWp.le
    convert h using 1
    ring
  have hyc : |p.2|/W ≤ (2*Real.pi)*(‖markedMajorFourierFrequency p‖/W) := by
    have h := div_le_div_of_nonneg_right hy' hWp.le
    convert h using 1
    ring
  have hxw : 1+|p.1|/W ≤ (2*Real.pi)*(1+‖markedMajorFourierFrequency p‖/W) := by nlinarith
  have hyw : 1+|p.2|/W ≤ (2*Real.pi)*(1+‖markedMajorFourierFrequency p‖/W) := by nlinarith
  calc
    _ ≤ ((2*Real.pi)*(1+‖markedMajorFourierFrequency p‖/W))^N*
        ((2*Real.pi)*(1+‖markedMajorFourierFrequency p‖/W))^N := by
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hxw N)
        (pow_le_pow_left₀ (by positivity) hyw N) (by positivity) (by positivity)
    _ = _ := by rw [← pow_add, mul_pow, show N+N = 2*N by omega]

def markedMajorFourierDecayConstant (N : ℕ) : ℝ :=
  (2*Real.pi)^(2*N)*2^(2*N)*(1+2^(2*N)*((2*N+1 : ℕ) : ℝ))

theorem markedMajorFourierDecayConstant_pos (N : ℕ) :
    0 < markedMajorFourierDecayConstant N := by unfold markedMajorFourierDecayConstant; positivity

theorem markedMajorFourierCoefficient_scaled_weighted (g : SchwartzMap (ℝ × ℝ) ℂ)
    (N : ℕ) {C W : ℝ} (hC : 0 ≤ C) (hW : 1 ≤ W)
    (hD : ∀ k ≤ 2*N, (∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k g p‖) ≤ C*W^k)
    (p : ℝ × ℝ) :
    (1+|p.1|/W)^N*(1+|p.2|/W)^N*‖markedMajorFourierCoefficient g p‖ ≤
      markedMajorFourierDecayConstant N*C := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  have hcoef := markedMajorFourierCoefficient_norm_le g p
  have hw := markedMajorFourierFrequency_coordinate_weights N hW p
  have hr := markedMajorPlaneLift_fourier_scaled_radial g (2*N) hC hW hD
    (markedMajorFourierFrequency p)
  calc
    _ ≤ (1+|p.1|/W)^N*(1+|p.2|/W)^N*
        ‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ)
          (markedMajorFourierFrequency p)‖ := mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ ≤ ((2*Real.pi)^(2*N)*(1+‖markedMajorFourierFrequency p‖/W)^(2*N))*
        ‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ)
          (markedMajorFourierFrequency p)‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = (2*Real.pi)^(2*N)*((1+‖markedMajorFourierFrequency p‖/W)^(2*N)*
        ‖(𝓕 (markedMajorPlaneLift g) : SchwartzMap MarkedMajorFourierPlane ℂ)
          (markedMajorFourierFrequency p)‖) := by ring
    _ ≤ (2*Real.pi)^(2*N)*((2^(2*N)*(1+2^(2*N)*((2*N+1 : ℕ) : ℝ)))*C) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by unfold markedMajorFourierDecayConstant; ring

theorem markedMajorFourierCoefficient_scaled_div (g : SchwartzMap (ℝ × ℝ) ℂ)
    (N : ℕ) {C W : ℝ} (hC : 0 ≤ C) (hW : 1 ≤ W)
    (hD : ∀ k ≤ 2*N, (∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k g p‖) ≤ C*W^k)
    (p : ℝ × ℝ) :
    ‖markedMajorFourierCoefficient g p‖ ≤ markedMajorFourierDecayConstant N*C/
      ((1+|p.1|/W)^N*(1+|p.2|/W)^N) := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  apply (le_div_iff₀ (by positivity)).mpr
  convert markedMajorFourierCoefficient_scaled_weighted g N hC hW hD p using 1
  ring

theorem markedMajorFourierCoefficient_scaled_decay (g : SchwartzMap (ℝ × ℝ) ℂ)
    (N : ℕ) {C W : ℝ} (hC : 0 ≤ C) (hW : 1 ≤ W)
    (hD : ∀ k ≤ 2*N, (∫ p : ℝ × ℝ, ‖iteratedFDeriv ℝ k g p‖) ≤ C*W^k)
    (p : ℝ × ℝ) :
    ‖markedMajorFourierCoefficient g p‖ ≤
      markedMajorFourierDecayConstant N*C*(1+|p.1|/W)^(-(N : ℝ))*
        (1+|p.2|/W)^(-(N : ℝ)) := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  have hx : (1+|p.1|/W)^(-(N : ℝ)) = ((1+|p.1|/W)^N)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hy : (1+|p.2|/W)^(-(N : ℝ)) = ((1+|p.2|/W)^N)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  convert markedMajorFourierCoefficient_scaled_div g N hC hW hD p using 1
  rw [hx,hy]
  ring

end
end ArtinMatthews
