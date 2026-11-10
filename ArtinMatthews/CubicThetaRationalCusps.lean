module

public import ArtinMatthews.CubicThetaRationalTwist
public import ArtinMatthews.CubicThetaRationalCuspGeometry
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Finite rational cusp limits from actual finite norm-phase cancellation. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators MatrixGroups Topology
open Complex UpperHalfPlane Filter

/-- For any periodic weight, the finite norm-phase sum is precisely the
condition that removes the constant term at a rational cusp. The Möbius
map, normalization, rational translation, and Poisson limit are all proved. -/
theorem tendsto_weightedEisensteinTheta_cusp_of_twist_sum_zero
    {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (γ : SL(2, ℤ))
    (hc : γ 1 0 ≠ 0) (k : ℤ) (hk : (N : ℤ) = γ 1 0 * k)
    (hsum : ∑ r, eisensteinRationalTwist w (γ 0 0 * k) r = 0) :
    Tendsto (fun τ : ℍ => weightedEisensteinTheta w (γ • τ) /
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) atImInfty (𝓝 0) := by
  have hr : (γ 0 0 : ℝ) / (γ 1 0 : ℝ) = ((γ 0 0 * k : ℤ) : ℝ) / N := by
    have hkR : (N : ℝ) = (γ 1 0 : ℝ) * (k : ℝ) := by exact_mod_cast hk
    have hcR : (γ 1 0 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
    have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    push_cast
    field_simp
    rw [hkR]
    ring
  have hlim := (tendsto_weightedEisensteinTheta_fricke_zero
    (eisensteinRationalTwist w (γ 0 0 * k)) hsum).comp
      (eisensteinCuspAux_tendsto N γ hc)
  have hscaled := hlim.mul_const ((γ 1 0 : ℂ) / (3 * (N : ℂ) ^ 2))
  have he (τ : ℍ) : weightedEisensteinTheta w (γ • τ) /
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) =
      (weightedEisensteinTheta (eisensteinRationalTwist w (γ 0 0 * k))
        (eisensteinPeriodFricke N (eisensteinCuspAux N γ hc τ)) /
          (eisensteinCuspAux N γ hc τ : ℂ)) *
        ((γ 1 0 : ℂ) / (3 * (N : ℂ) ^ 2)) := by
    rw [eisensteinCuspAux_decomposition N γ hc τ, hr,
      weightedEisensteinTheta_rational_translate]
    rw [← eisensteinCuspAux_normalization N γ hc τ]
    exact (div_mul_div_cancel₀ (eisensteinCuspAux N γ hc τ).ne_zero).symm
  simpa only [Function.comp_def, ← he, zero_mul] using hscaled

end ArtinMatthews
