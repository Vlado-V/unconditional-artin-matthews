module

public import ArtinMatthews.SourceKPLocalMatrixHeight
public import ArtinMatthews.SourceArchSphericalSection
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete inverse-entry bound for every complex right translate. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

def sourceArchMatrixHeightConstant (g : GL (Fin 2) ℂ) : ℝ :=
  max 1 (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * sourceKPEntryBound g⁻¹ ^ 2)

theorem sourceArchMatrixHeightConstant_pos (g : GL (Fin 2) ℂ) :
    0 < sourceArchMatrixHeightConstant g := by
  unfold sourceArchMatrixHeightConstant
  positivity

theorem sourceArchBottomMax_sq_le (g : GL (Fin 2) ℂ) :
    sourceKPBottomMax g ^ 2 ≤ sourceArchBottomNorm g := by
  unfold sourceKPBottomMax sourceArchBottomNorm
  by_cases h : ‖g 1 0‖ ≤ ‖g 1 1‖
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · rw [max_eq_left (le_of_not_ge h)]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem sourceArchHeight_translate (g : GL (Fin 2) ℂ) (x : ℂ) :
    sourceArchHeight ((sourceGL2Weyl * sourceGL2Upper x) * g) ≤
      sourceArchMatrixHeightConstant g * (max 1 ‖x‖)⁻¹ ^ 2 := by
  let h : GL (Fin 2) ℂ := sourceGL2Weyl * sourceGL2Upper x
  let R := sourceKPBottomMax (h * g)
  let D := sourceArchBottomNorm (h * g)
  let M := sourceKPEntryBound g⁻¹
  let X := max 1 ‖x‖
  have hR : 0 < R := sourceKPBottomMax_pos _
  have hD : 0 < D := sourceArchBottomNorm_pos _
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM : 0 ≤ M := le_trans (by norm_num) (sourceKPEntryBound_one_le _)
  have hb : X ≤ 2 * M * R := by
    simpa only [h, X, M, R, sourceKPBottomMax_weyl_upper] using sourceKPBottomMax_mul_inverse_bound h g
  have hsq : X ^ 2 ≤ 4 * M ^ 2 * R ^ 2 := by
    have hs := (sq_le_sq₀ hX.le (by positivity : 0 ≤ 2 * M * R)).mpr hb
    nlinarith
  have hsqD : X ^ 2 ≤ 4 * M ^ 2 * D :=
    hsq.trans (mul_le_mul_of_nonneg_left (sourceArchBottomMax_sq_le (h * g)) (by positivity))
  have hd : 0 ≤ ‖(GeneralLinearGroup.det g : ℂ)‖ := norm_nonneg _
  have hraw : ‖(GeneralLinearGroup.det g : ℂ)‖ / D ≤
      (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * M ^ 2) / X ^ 2 := by
    apply (div_le_div_iff₀ hD (sq_pos_of_pos hX)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsqD hd]
  have hdet : ‖(GeneralLinearGroup.det (h * g) : ℂ)‖ = ‖(GeneralLinearGroup.det g : ℂ)‖ := by
    rw [map_mul, Units.val_mul, norm_mul,
      show ‖(GeneralLinearGroup.det h : ℂ)‖ = 1 from sourceKPDetNorm_weyl_upper x, one_mul]
  change ‖(GeneralLinearGroup.det (h * g) : ℂ)‖ / D ≤ _
  rw [hdet, sourceArchMatrixHeightConstant]
  calc
    _ ≤ (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * M ^ 2) / X ^ 2 := hraw
    _ ≤ max 1 (4 * ‖(GeneralLinearGroup.det g : ℂ)‖ * M ^ 2) / X ^ 2 :=
      div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg X)
    _ = _ := by dsimp only [M, X]; rw [div_eq_mul_inv, inv_pow]

end
end ArtinMatthews.SourceArchJacquet
