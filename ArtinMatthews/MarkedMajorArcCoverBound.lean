module

public import ArtinMatthews.MarkedMajorArcCircleSource
public import ArtinMatthews.MarkedMajorArcCircleLift
import ArtinMatthews.MarkedMinorArcShearOperator
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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

/-! Transfer from the actual uniformly normalized rational arcs to the original
circle major-kernel sum. The finite union is a cover and may overlap. -/
namespace ArtinMatthews
open Finset MeasureTheory
open scoped ENNReal
noncomputable section
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

 theorem markedMajorCircleSource_norm_on_major (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) {Q Y C : ℝ} (hQ : 0 ≤ Q) (hY : 0 < Y)
    (hbound : ∀ (q : ℕ),0 < q → (q:ℝ) ≤ Q → ∀ (h : ℤ) (θ : ℝ),|θ| ≤ 2*Q →
      ‖(Y:ℂ)⁻¹*markedMajorArcSourceSum S T A B ψ q h θ Y‖ ≤ C)
    (ξ : AddCircle (1:ℝ)) (hξ : ξ ∈ markedMinorCircleMajor Q Y) :
    ‖markedMajorCircleSource S T A B ψ Y ξ‖ ≤ Y*C := by
  obtain ⟨q,h,θ,hq,hqQ,_,hθ,he⟩ := markedMajor_circle_major_lift hQ hY ξ hξ
  have hb := hbound q hq hqQ h θ hθ
  have hh : markedMajorCircleSource S T A B ψ Y ξ =
      (Y:ℂ)*((Y:ℂ)⁻¹*markedMajorArcSourceSum S T A B ψ q h θ Y) := by
    rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr hY.ne')]
    rw [← he]
    exact markedMajorCircleSource_arc S T A B ψ q h θ Y
  rw [hh,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY]
  exact mul_le_mul_of_nonneg_left hb hY.le

 theorem markedMajorKernelSource_norm_of_arcs (S T : Finset (ℕ×(ℕ×ℕ)))
    (A B : ℕ×(ℕ×ℕ) → ℂ) (ψ : ℝ → ℂ) {Q Y C : ℝ} (hQ : 0 ≤ Q) (hY : 0 < Y) (hC : 0 ≤ C)
    (hbound : ∀ (q : ℕ),0 < q → (q:ℝ) ≤ Q → ∀ (h : ℤ) (θ : ℝ),|θ| ≤ 2*Q →
      ‖(Y:ℂ)⁻¹*markedMajorArcSourceSum S T A B ψ q h θ Y‖ ≤ C) :
    ‖markedMajorKernelSource S T A B ψ Q Y‖ ≤ 4*Q^3*C := by
  rw [markedMajorKernelSource_eq_integral]
  have hv : (volume : Measure (AddCircle (1:ℝ)))=AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using
      (AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ)))
  have hn := norm_setIntegral_le_of_norm_le_const
    (by finiteness : AddCircle.haarAddCircle (markedMinorCircleMajor Q Y) < ⊤)
    (markedMajorCircleSource_norm_on_major S T A B ψ hQ hY hbound)
  rw [← hv] at hn ⊢
  calc
    _ ≤ volume.real (markedMinorCircleMajor Q Y)*(Y*C) := by simpa only [mul_comm] using hn
    _ ≤ (4*Q^3/Y)*(Y*C) := mul_le_mul_of_nonneg_right
      (markedBan_major_real_measure_le hQ hY) (mul_nonneg hY.le hC)
    _ = _ := by field_simp

end
end ArtinMatthews
