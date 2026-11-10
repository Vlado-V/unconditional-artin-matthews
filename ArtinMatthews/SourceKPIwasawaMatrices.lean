module

public import ArtinMatthews.SourceKPNormalizedBorel
public import ArtinMatthews.SourceKPIntegralGroup
public import ArtinMatthews.SourceKPIntegralGeneration
public import ArtinMatthews.SourceKubotaBottomRows
public import ArtinMatthews.SourceKubotaGL2Generation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Integral right row operations give the actual rank-two Iwasawa
decomposition. At each branch the selected bottom denominator is
nonzero and its valuation controls the integral root parameter. -/

namespace ArtinMatthews
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section
variable {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (ν : Valuation F Γ)

theorem sourceKPIntegralMatrix_lower (x : F) (hx : ν x ≤ 1) :
    SourceKPIntegralMatrix ν (sourceGL2Lower x) := by
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [sourceGL2Lower, hx]
  · rw [sourceGL2Lower_det, Units.val_one, map_one]

theorem sourceGL2_right_lower_bottom_left (g : GL (Fin 2) F) (x : F) :
    (g * sourceGL2Lower x) 1 0 = g 1 0 + g 1 1 * x := by
  simp [sourceGL2_bottom_left_mul, sourceGL2Lower]

theorem sourceKPIwasawa_right_triangular (g : GL (Fin 2) F) :
    ∃ k : GL (Fin 2) F, SourceKPIntegralMatrix ν k ∧ (g * k) 1 0 = 0 := by
  by_cases h : ν (g 1 0) ≤ ν (g 1 1)
  · have hd : g 1 1 ≠ 0 := by
      intro hz
      have hc : ν (g 1 0) = 0 := by
        rw [hz, map_zero] at h
        exact le_antisymm h zero_le
      have hc₀ : g 1 0 = 0 := by
        by_contra hn
        exact (ne_of_gt (ν.pos_iff.mpr hn)) hc
      exact sourceGL2_bottom_right_ne_zero g hc₀ hz
    let x := -(g 1 0 / g 1 1)
    have hx : ν x ≤ 1 := by
      dsimp only [x]
      rw [ν.map_neg, map_div₀]
      exact (div_le_one₀ (ν.pos_iff.mpr hd)).mpr h
    refine ⟨sourceGL2Lower x, sourceKPIntegralMatrix_lower ν x hx, ?_⟩
    rw [sourceGL2_right_lower_bottom_left]
    dsimp only [x]
    rw [mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hd, add_neg_cancel]
  · have hc : g 1 0 ≠ 0 := by
      intro hz
      rw [hz, map_zero] at h
      exact h zero_le
    let x := -(g 1 1 / g 1 0)
    have hx : ν x ≤ 1 := by
      dsimp only [x]
      rw [ν.map_neg, map_div₀]
      exact (div_le_one₀ (ν.pos_iff.mpr hc)).mpr (le_of_lt (lt_of_not_ge h))
    refine ⟨sourceGL2Upper x * sourceGL2Weyl,
      sourceKPIntegralMatrix_mul ν (sourceKPIntegralMatrix_upper ν x hx) (sourceKPIntegralMatrix_weyl ν), ?_⟩
    rw [← mul_assoc, sourceGL2_right_weyl_bottom_left, sourceGL2_right_upper_bottom_right]
    dsimp only [x]
    rw [mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hc, neg_add_cancel]

theorem sourceKPIwasawa_matrix_factor (g : GL (Fin 2) F) :
    ∃ (b : GL (Fin 2) F) (d : Fˣ) (k : GL (Fin 2) F),
      b ∈ sourceGL2NormalizedBorel F ∧ SourceKPIntegralMatrix ν k ∧
      g = b * GeneralLinearGroup.scalar (Fin 2) d * k := by
  obtain ⟨k, hk, htri⟩ := sourceKPIwasawa_right_triangular ν g
  obtain ⟨x, u, d, hfactor⟩ := sourceGL2_triangular_factor (g * k) htri
  refine ⟨sourceGL2Upper x * sourceGL2Diagonal u, d, k⁻¹,
    (sourceGL2NormalizedBorel F).mul_mem (sourceGL2NormalizedBorel_upper F x)
      (sourceGL2NormalizedBorel_diagonal F u), sourceKPIntegralMatrix_inv ν hk, ?_⟩
  rw [← hfactor, mul_assoc, mul_inv_cancel, mul_one]

end
end ArtinMatthews
