module

public import ArtinMatthews.CubicTheta
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
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

/-! The normalized infinite-cusp limit for the actual ideal theta series. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups Topology
open Complex UpperHalfPlane Filter

/-- Upper-triangular rational cusp representatives preserve approach to
imaginary infinity, so the actual ideal theta remains zero after weight-one
normalization. No modularity is used. -/
theorem tendsto_heckeTheta_cusp_of_lowerLeft_zero
    (χ : OAI.SevenEighths.HeckeFamily.Character) (γ : SL(2, ℤ)) (hc : γ 1 0 = 0) :
    Tendsto (fun τ : ℍ => heckeTheta χ (γ • τ) /
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) atImInfty (𝓝 0) := by
  have hγ : Tendsto (fun τ : ℍ => γ • τ) atImInfty atImInfty := by
    change Tendsto (fun τ : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ)
      atImInfty atImInfty
    apply UpperHalfPlane.tendsto_smul_atImInfty
    change (algebraMap ℤ ℝ (γ 1 0)) = 0
    simp [hc]
  have hzero : Tendsto (heckeTheta χ) atImInfty (𝓝 0) := heckeTheta_zeroAtInfty χ
  have h := (hzero.comp hγ).div_const (γ 1 1 : ℂ)
  simpa only [Function.comp_def, hc, Int.cast_zero, zero_mul, zero_add, zero_div] using h

end ArtinMatthews
