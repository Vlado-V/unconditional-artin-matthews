module

public import ArtinMatthews.SourceFiniteKPTameUnits
public import ArtinMatthews.SourceKPIntegralGroup
public import ArtinMatthews.SourceKPNormalizedBorel
public import ArtinMatthews.SourceFiniteIwasawaHeight
public import ArtinMatthews.SourceKPIwasawaMatrices
public import ArtinMatthews.SourceKubotaBottomRows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Local matrix heights and explicit right-translation bounds. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

section NormedField
variable {F : Type*} [NormedField F]

def sourceKPBottomMax (g : GL (Fin 2) F) : ℝ := max ‖g 1 0‖ ‖g 1 1‖

def sourceKPEntryBound (g : GL (Fin 2) F) : ℝ :=
  max 1 (max (max ‖g 0 0‖ ‖g 0 1‖) (max ‖g 1 0‖ ‖g 1 1‖))

theorem sourceKPEntryBound_one_le (g : GL (Fin 2) F) : 1 ≤ sourceKPEntryBound g := le_max_left _ _

theorem sourceKPEntryBound_entry (g : GL (Fin 2) F) (i j : Fin 2) :
    ‖g i j‖ ≤ sourceKPEntryBound g := by
  have h₀ : max ‖g 0 0‖ ‖g 0 1‖ ≤ sourceKPEntryBound g :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₁ : max ‖g 1 0‖ ‖g 1 1‖ ≤ sourceKPEntryBound g :=
    (le_max_right _ _).trans (le_max_right _ _)
  fin_cases i <;> fin_cases j
  · exact (le_max_left _ _).trans h₀
  · exact (le_max_right _ _).trans h₀
  · exact (le_max_left _ _).trans h₁
  · exact (le_max_right _ _).trans h₁

theorem sourceKPBottomMax_pos (g : GL (Fin 2) F) : 0 < sourceKPBottomMax g := by
  by_cases h : g 1 0 = 0
  · exact lt_of_lt_of_le (norm_pos_iff.mpr (sourceGL2_bottom_right_ne_zero g h)) (le_max_right _ _)
  · exact lt_of_lt_of_le (norm_pos_iff.mpr h) (le_max_left _ _)

theorem sourceKPBottomMax_mul_inverse_bound (h g : GL (Fin 2) F) :
    sourceKPBottomMax h ≤ 2 * sourceKPEntryBound g⁻¹ * sourceKPBottomMax (h * g) := by
  let r := h * g
  let M := sourceKPEntryBound g⁻¹
  let R := sourceKPBottomMax r
  have hM : 0 ≤ M := (by dsimp only [M]; exact (sourceKPEntryBound_one_le g⁻¹).trans' (by norm_num))
  have hR : 0 ≤ R := (sourceKPBottomMax_pos r).le
  have h₀ : ‖r 1 0‖ ≤ R := le_max_left _ _
  have h₁ : ‖r 1 1‖ ≤ R := le_max_right _ _
  have he : h = r * g⁻¹ := by dsimp only [r]; simp
  have bound (j : Fin 2) : ‖h 1 j‖ ≤ 2 * M * R := by
    rw [he]
    change ‖((r : Matrix (Fin 2) (Fin 2) F) * (g⁻¹ : GL (Fin 2) F)) 1 j‖ ≤ _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    calc
      _ ≤ ‖r 1 0 * g⁻¹ 0 j‖ + ‖r 1 1 * g⁻¹ 1 j‖ := norm_add_le _ _
      _ = ‖r 1 0‖ * ‖g⁻¹ 0 j‖ + ‖r 1 1‖ * ‖g⁻¹ 1 j‖ := by rw [norm_mul, norm_mul]
      _ ≤ R * M + R * M := add_le_add
        (mul_le_mul h₀ (sourceKPEntryBound_entry g⁻¹ 0 j) (norm_nonneg _) hR)
        (mul_le_mul h₁ (sourceKPEntryBound_entry g⁻¹ 1 j) (norm_nonneg _) hR)
      _ = _ := by ring
  exact max_le (bound 0) (bound 1)

theorem sourceKPBottomMax_weyl_upper (x : F) :
    sourceKPBottomMax (sourceGL2Weyl * sourceGL2Upper x) = max 1 ‖x‖ := by
  simp [sourceKPBottomMax, sourceGL2Weyl, sourceGL2Upper, Matrix.mul_apply, Fin.sum_univ_two]

theorem sourceKPDetNorm_weyl_upper (x : F) :
    ‖(GeneralLinearGroup.det (sourceGL2Weyl * sourceGL2Upper x) : F)‖ = 1 := by
  simp [map_mul, sourceGL2Weyl, sourceGL2Upper, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

end NormedField

variable (K : Type) [Field K] [NumberField K]

def sourceKPFiniteMatrixHeight (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K)) : ℝ :=
  ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ / sourceKPBottomMax g ^ 2

theorem sourceKPFiniteMatrixHeight_pos (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K)) : 0 < sourceKPFiniteMatrixHeight K P g :=
  div_pos (norm_pos_iff.mpr (GeneralLinearGroup.det g).ne_zero)
    (sq_pos_of_pos (sourceKPBottomMax_pos g))

theorem sourceKPFiniteMatrixHeight_borel (P : HeightOneSpectrum (𝓞 K))
    (b g : GL (Fin 2) (P.adicCompletion K))
    (hb : b ∈ sourceGL2NormalizedBorel (P.adicCompletion K)) :
    sourceKPFiniteMatrixHeight K P (b * g) =
      ‖(GeneralLinearGroup.det b : P.adicCompletion K)‖ * sourceKPFiniteMatrixHeight K P g := by
  have hbottom : sourceKPBottomMax (b * g) = sourceKPBottomMax g := by
    simp only [sourceKPBottomMax, sourceGL2_bottom_left_mul, sourceGL2_bottom_right_mul,
      hb.1, hb.2, zero_mul, one_mul, zero_add]
  rw [sourceKPFiniteMatrixHeight, hbottom, map_mul, Units.val_mul, norm_mul,
    mul_div_assoc, sourceKPFiniteMatrixHeight]

theorem sourceKPFiniteMatrixHeight_scalar (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K)) (u : (P.adicCompletion K)ˣ) :
    sourceKPFiniteMatrixHeight K P (g * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceKPFiniteMatrixHeight K P g := by
  have hbottom : sourceKPBottomMax (g * GeneralLinearGroup.scalar (Fin 2) u) =
      sourceKPBottomMax g * ‖(u : P.adicCompletion K)‖ := by
    simp only [sourceKPBottomMax, sourceKPMatrix_right_scalar_entry, norm_mul]
    exact (max_mul_of_nonneg _ _ (norm_nonneg _)).symm
  rw [sourceKPFiniteMatrixHeight, hbottom, mul_pow, map_mul, GeneralLinearGroup.det_scalar]
  simp only [Fintype.card_fin, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow]
  exact mul_div_mul_right _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr u.ne_zero))

theorem sourceKPFiniteMatrixHeight_integral (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K))
    (hg : SourceKPIntegralMatrix (sourceKPFiniteVal K P) g) :
    sourceKPFiniteMatrixHeight K P g = 1 := by
  have h := sourceKPIwasawa_torus_norm K P g 1 1 g (by simp [sourceGL2NormalizedBorel]) hg (by simp)
  simpa [sourceKPFiniteMatrixHeight, sourceKPBottomMax] using h.symm

theorem sourceKPFiniteMatrixHeight_right_integral (P : HeightOneSpectrum (𝓞 K))
    (h g : GL (Fin 2) (P.adicCompletion K))
    (hg : SourceKPIntegralMatrix (sourceKPFiniteVal K P) g) :
    sourceKPFiniteMatrixHeight K P (h * g) = sourceKPFiniteMatrixHeight K P h := by
  obtain ⟨b, d, k, hb, hk, he⟩ := sourceKPIwasawa_matrix_factor (sourceKPFiniteVal K P) h
  have he' : h * g = b * GeneralLinearGroup.scalar (Fin 2) d * (k * g) := by rw [he, mul_assoc]
  have h₁ := sourceKPIwasawa_torus_norm K P h b d k hb hk he
  have h₂ := sourceKPIwasawa_torus_norm K P (h * g) b d (k * g) hb
    (sourceKPIntegralMatrix_mul _ hk hg) he'
  exact h₂.symm.trans h₁

theorem sourceKPFiniteMatrixHeight_weyl_upper (P : HeightOneSpectrum (𝓞 K))
    (x : P.adicCompletion K) :
    sourceKPFiniteMatrixHeight K P (sourceGL2Weyl * sourceGL2Upper x) = (max 1 ‖x‖)⁻¹ ^ 2 := by
  rw [sourceKPFiniteMatrixHeight, sourceKPBottomMax_weyl_upper, sourceKPDetNorm_weyl_upper,
    one_div, inv_pow]

def sourceKPFiniteMatrixHeightConstant (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K)) : ℝ := by
  classical
  exact if SourceKPIntegralMatrix (sourceKPFiniteVal K P) g then 1 else
    max 1 (4 * ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ * sourceKPEntryBound g⁻¹ ^ 2)

theorem sourceKPFiniteMatrixHeightConstant_pos (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K)) : 0 < sourceKPFiniteMatrixHeightConstant K P g := by
  classical
  unfold sourceKPFiniteMatrixHeightConstant
  split_ifs <;> positivity

theorem sourceKPFiniteMatrixHeightConstant_integral (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K))
    (hg : SourceKPIntegralMatrix (sourceKPFiniteVal K P) g) :
    sourceKPFiniteMatrixHeightConstant K P g = 1 := by
  classical
  simp only [sourceKPFiniteMatrixHeightConstant, ite_eq_left hg]

theorem sourceKPFiniteMatrixHeight_translate (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K)) (x : P.adicCompletion K) :
    sourceKPFiniteMatrixHeight K P ((sourceGL2Weyl * sourceGL2Upper x) * g) ≤
      sourceKPFiniteMatrixHeightConstant K P g * (max 1 ‖x‖)⁻¹ ^ 2 := by
  classical
  by_cases hg : SourceKPIntegralMatrix (sourceKPFiniteVal K P) g
  · rw [sourceKPFiniteMatrixHeight_right_integral K P _ g hg,
      sourceKPFiniteMatrixHeight_weyl_upper, sourceKPFiniteMatrixHeightConstant_integral K P g hg,
      one_mul]
  · let h : GL (Fin 2) (P.adicCompletion K) := sourceGL2Weyl * sourceGL2Upper x
    let R := sourceKPBottomMax (h * g)
    let M := sourceKPEntryBound g⁻¹
    let X := max 1 ‖x‖
    have hR : 0 < R := sourceKPBottomMax_pos _
    have hX : 0 < X := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hM : 0 ≤ M := le_trans (by norm_num) (sourceKPEntryBound_one_le _)
    have hb : X ≤ 2 * M * R := by
      simpa only [h, X, M, R, sourceKPBottomMax_weyl_upper] using sourceKPBottomMax_mul_inverse_bound h g
    have hsq : X ^ 2 ≤ 4 * M ^ 2 * R ^ 2 := by nlinarith
    have hd : 0 ≤ ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ := norm_nonneg _
    have hraw : ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ / R ^ 2 ≤
        (4 * ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ * M ^ 2) / X ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hR) (sq_pos_of_pos hX)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq hd]
    have hdet : ‖(GeneralLinearGroup.det (h * g) : P.adicCompletion K)‖ =
        ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ := by
      rw [map_mul, Units.val_mul, norm_mul, show ‖(GeneralLinearGroup.det h : P.adicCompletion K)‖ = 1 from sourceKPDetNorm_weyl_upper x, one_mul]
    change ‖(GeneralLinearGroup.det (h * g) : P.adicCompletion K)‖ / R ^ 2 ≤ _
    rw [hdet, sourceKPFiniteMatrixHeightConstant, ite_eq_right hg]
    calc
      _ ≤ (4 * ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ * M ^ 2) / X ^ 2 := hraw
      _ ≤ max 1 (4 * ‖(GeneralLinearGroup.det g : P.adicCompletion K)‖ * M ^ 2) / X ^ 2 :=
        div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg X)
      _ = _ := by dsimp only [M, X]; rw [div_eq_mul_inv, inv_pow]

end
end ArtinMatthews
