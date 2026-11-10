module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import ArtinMatthews.SourceKubotaBottomRows
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The literal rank-two integral matrix subgroup for a valued field.
Entries have valuation at most one and determinant has valuation one.
Closure, inverse, and the existence of a unit in the bottom row are
proved from the matrix operations. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (ν : Valuation F Γ)

structure SourceKPIntegralMatrix (g : GL (Fin 2) F) : Prop where
  entries : ∀ i j, ν (g i j) ≤ 1
  det_unit : ν ((GeneralLinearGroup.det g : Fˣ) : F) = 1

theorem sourceGL2_inverse_adjugate (g : GL (Fin 2) F) :
    ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (((GeneralLinearGroup.det g : Fˣ) : F)⁻¹) • (g : Matrix (Fin 2) (Fin 2) F).adjugate := by
  let A := (g : Matrix (Fin 2) (Fin 2) F)
  have h : IsUnit A.det := (GeneralLinearGroup.det g).isUnit
  have hh : (h.unit : F) = ((GeneralLinearGroup.det g : Fˣ) : F) := h.unit_spec
  rw [GeneralLinearGroup.coe_inv, Matrix.nonsing_inv_apply _ h, Units.val_inv_eq_inv_val, hh]

theorem sourceKPIntegralMatrix_one : SourceKPIntegralMatrix ν (1 : GL (Fin 2) F) := by
  refine ⟨?_, ?_⟩
  · intro i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  · simp

theorem sourceKPIntegralMatrix_mul {g h : GL (Fin 2) F}
    (hg : SourceKPIntegralMatrix ν g) (hh : SourceKPIntegralMatrix ν h) :
    SourceKPIntegralMatrix ν (g * h) := by
  refine ⟨?_, ?_⟩
  · intro i j
    change ν (((g : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F)) i j) ≤ 1
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    apply (ν.map_add _ _).trans
    apply max_le
    · rw [map_mul]
      exact (mul_le_mul_of_nonneg_right (hg.entries i 0) zero_le).trans
        (by simpa only [one_mul] using hh.entries 0 j)
    · rw [map_mul]
      exact (mul_le_mul_of_nonneg_right (hg.entries i 1) zero_le).trans
        (by simpa only [one_mul] using hh.entries 1 j)
  · rw [map_mul, Units.val_mul, map_mul, hg.det_unit, hh.det_unit, mul_one]

theorem sourceKPIntegralMatrix_inv {g : GL (Fin 2) F}
    (hg : SourceKPIntegralMatrix ν g) : SourceKPIntegralMatrix ν g⁻¹ := by
  refine ⟨?_, ?_⟩
  · intro i j
    rw [sourceGL2_inverse_adjugate, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀,
      hg.det_unit, inv_one, one_mul, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [hg.entries]
  · rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, hg.det_unit, inv_one]

def sourceKPIntegralGroup : Subgroup (GL (Fin 2) F) where
  carrier := {g | SourceKPIntegralMatrix ν g}
  one_mem' := sourceKPIntegralMatrix_one ν
  mul_mem' := sourceKPIntegralMatrix_mul ν
  inv_mem' := sourceKPIntegralMatrix_inv ν

theorem sourceKPIntegralMatrix_bottom_unit {g : GL (Fin 2) F}
    (hg : SourceKPIntegralMatrix ν g) : ν (g 1 0) = 1 ∨ ν (g 1 1) = 1 := by
  by_contra h
  push Not at h
  have hc := lt_of_le_of_ne (hg.entries 1 0) h.1
  have hd := lt_of_le_of_ne (hg.entries 1 1) h.2
  have h₁ : ν (g 0 0 * g 1 1) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (hg.entries 0 0) zero_le).trans_lt (by simpa only [one_mul] using hd)
  have h₂ : ν (g 0 1 * g 1 0) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (hg.entries 0 1) zero_le).trans_lt (by simpa only [one_mul] using hc)
  have hl := (ν.map_sub _ _).trans_lt (max_lt h₁ h₂)
  rw [← sourceGL2_det_val, hg.det_unit] at hl
  exact (lt_irrefl 1) hl

end
end ArtinMatthews
