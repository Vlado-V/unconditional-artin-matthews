module

public import ArtinMatthews.SourceArchMatrixHeight
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

/-! Local height comparison for arbitrary right multiplication. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

theorem sourceKPNormedMatrixHeight_mul_bound {F : Type*} [NormedField F]
    (g h : GL (Fin 2) F) :
    ‖(GeneralLinearGroup.det (g * h) : F)‖ / sourceKPBottomMax (g * h) ^ 2 ≤
      (4 * ‖(GeneralLinearGroup.det h : F)‖ * sourceKPEntryBound h⁻¹ ^ 2) *
        (‖(GeneralLinearGroup.det g : F)‖ / sourceKPBottomMax g ^ 2) := by
  let R := sourceKPBottomMax (g * h)
  let X := sourceKPBottomMax g
  let M := sourceKPEntryBound h⁻¹
  have hR : 0 < R := sourceKPBottomMax_pos _
  have hX : 0 < X := sourceKPBottomMax_pos _
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (sourceKPEntryBound_one_le _)
  have hb : X ≤ 2 * M * R := sourceKPBottomMax_mul_inverse_bound g h
  have hsq : X ^ 2 ≤ 4 * M ^ 2 * R ^ 2 := by
    have hs := (sq_le_sq₀ hX.le (by positivity : 0 ≤ 2 * M * R)).mpr hb
    nlinarith
  rw [map_mul, Units.val_mul, norm_mul, ← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos hR) (sq_pos_of_pos hX)).mpr
  have hs := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (norm_nonneg (GeneralLinearGroup.det g : F))
      (norm_nonneg (GeneralLinearGroup.det h : F)))
  dsimp only [M] at hs
  nlinarith

theorem sourceKPFiniteMatrixHeight_mul_le (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (g h : GL (Fin 2) (P.adicCompletion K)) :
    sourceKPFiniteMatrixHeight K P (g * h) ≤
      sourceKPFiniteMatrixHeightConstant K P h * sourceKPFiniteMatrixHeight K P g := by
  classical
  by_cases hh : SourceKPIntegralMatrix (sourceKPFiniteVal K P) h
  · rw [sourceKPFiniteMatrixHeight_right_integral K P g h hh,
      sourceKPFiniteMatrixHeightConstant_integral K P h hh, one_mul]
  · have hb := sourceKPNormedMatrixHeight_mul_bound g h
    change sourceKPFiniteMatrixHeight K P (g * h) ≤
      (4 * ‖(GeneralLinearGroup.det h : P.adicCompletion K)‖ * sourceKPEntryBound h⁻¹ ^ 2) *
        sourceKPFiniteMatrixHeight K P g at hb
    apply hb.trans
    rw [sourceKPFiniteMatrixHeightConstant, ite_eq_right hh]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sourceKPFiniteMatrixHeight_pos K P g).le

namespace SourceArchJacquet

theorem sourceArchBottomNorm_mul_inverse_bound (g h : GL (Fin 2) ℂ) :
    sourceArchBottomNorm g ≤
      4 * sourceKPEntryBound h⁻¹ ^ 2 * sourceArchBottomNorm (g * h) := by
  let r := g * h
  let M := sourceKPEntryBound h⁻¹
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (sourceKPEntryBound_one_le _)
  have he : g = r * h⁻¹ := by dsimp only [r]; simp
  have hb (j : Fin 2) : ‖g 1 j‖ ≤ ‖r 1 0‖ * M + ‖r 1 1‖ * M := by
    rw [he]
    change ‖((r : Matrix (Fin 2) (Fin 2) ℂ) * (h⁻¹ : GL (Fin 2) ℂ)) 1 j‖ ≤ _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    calc
      _ ≤ ‖r 1 0 * h⁻¹ 0 j‖ + ‖r 1 1 * h⁻¹ 1 j‖ := norm_add_le _ _
      _ = ‖r 1 0‖ * ‖h⁻¹ 0 j‖ + ‖r 1 1‖ * ‖h⁻¹ 1 j‖ := by rw [norm_mul, norm_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (sourceKPEntryBound_entry h⁻¹ 0 j) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (sourceKPEntryBound_entry h⁻¹ 1 j) (norm_nonneg _))
  have hs (j : Fin 2) : ‖g 1 j‖ ^ 2 ≤ 2 * M ^ 2 * sourceArchBottomNorm r := by
    have hsquare := (sq_le_sq₀ (norm_nonneg (g 1 j))
      (by positivity : 0 ≤ ‖r 1 0‖ * M + ‖r 1 1‖ * M)).mpr (hb j)
    have hdiff := mul_nonneg (sq_nonneg (‖r 1 0‖ - ‖r 1 1‖)) (sq_nonneg M)
    dsimp only [sourceArchBottomNorm]
    nlinarith
  have h₀ := hs 0
  have h₁ := hs 1
  change ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 ≤ 4 * M ^ 2 * sourceArchBottomNorm r
  linarith

theorem sourceArchHeight_mul_le (g h : GL (Fin 2) ℂ) :
    sourceArchHeight (g * h) ≤ sourceArchMatrixHeightConstant h * sourceArchHeight g := by
  have hDg := sourceArchBottomNorm_pos g
  have hDr := sourceArchBottomNorm_pos (g * h)
  have hsq := sourceArchBottomNorm_mul_inverse_bound g h
  have hraw : sourceArchHeight (g * h) ≤
      (4 * ‖(GeneralLinearGroup.det h : ℂ)‖ * sourceKPEntryBound h⁻¹ ^ 2) * sourceArchHeight g := by
    unfold sourceArchHeight
    rw [map_mul, Units.val_mul, norm_mul, ← mul_div_assoc]
    apply (div_le_div_iff₀ hDr hDg).mpr
    have hs := mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (norm_nonneg (GeneralLinearGroup.det g : ℂ))
        (norm_nonneg (GeneralLinearGroup.det h : ℂ)))
    nlinarith
  exact hraw.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sourceArchHeight_pos g).le)

end SourceArchJacquet
end
end ArtinMatthews
