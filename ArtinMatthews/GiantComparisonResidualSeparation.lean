module

public import ArtinMatthews.GiantComparisonCellSeparation
public import ArtinMatthews.IdealResidualFamily
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal residual comparison coefficient separates on its two
logarithmic cells. Its sign and both inverse cell masses are retained. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem giantComparisonCellMarkTest_normalized_norm_le {I : Type*}
    [Fintype I] [DecidableEq I] (P : I → Finset ℕ) (h : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (j : ℤ) {Q : ℕ} (χ : IdealPrimitiveCharacters Q) (a : IdealSelectedLabels P) :
    ‖(ξ : ℂ) * giantComparisonCellMarkTest P h ξ j χ a‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
  exact (mul_le_mul_of_nonneg_left (giantComparisonCellMarkTest_norm_le P h hξ j χ a) hξ.le).trans_eq
    (mul_inv_cancel₀ hξ.ne')

theorem idealResidualCoefficient_eq_comparison_sum {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (A B : Finset (G × Fin k))
    (Q : ℕ) (h : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (a b : MarkedPhysicalMarking P (k+ell))
    (aux : GiantTwoSidedPatternAuxiliary P (idealResidualCopied (some (A,B)))) :
    let PA := idealResidualBands P A
    let PB := idealResidualBands P B
    let dA := idealResidualSelectedAuxiliary A
      (fun v hv => (mem_idealResidualFreeSlots (A ∪ B) v.1 v.2).mpr (mem_union_left B hv)) aux
    let dB := idealResidualSelectedAuxiliary B
      (fun v hv => (mem_idealResidualFreeSlots (A ∪ B) v.1 v.2).mpr (mem_union_right A hv)) aux
    idealResidualCoefficient P Q h ξ (some (A,B)) a b aux =
      (-(-1 : ℂ)^(A.card+B.card) * ((ξ : ℂ)⁻¹)^2) *
        ∑ l ∈ idealLogCells PB h, ∑ ψ : IdealPrimitiveCharacters Q,
          ∑ j ∈ idealLogCells PA h, ∑ χ : IdealPrimitiveCharacters Q,
            giantComparisonCellFreeTest PA h j χ dA *
              giantComparisonCellFreeTest PB h l ψ dB *
              ((ξ : ℂ) * giantComparisonCellMarkTest PB h ξ l ψ (idealResidualSelectedMarking B a)) *
              ((ξ : ℂ) * giantComparisonCellMarkTest PA h ξ j χ (idealResidualSelectedMarking A b)) := by
  intro PA PB dA dB
  change -(-1 : ℂ)^(A.card+B.card) *
    idealCharacterCellKernel PA Q h ξ dA (idealResidualSelectedMarking A b) *
    idealCharacterCellKernel PB Q h ξ dB (idealResidualSelectedMarking B a) = _
  rw [idealCharacterCellKernel_eq_comparison_sum PA Q h ξ dA,
    idealCharacterCellKernel_eq_comparison_sum PB Q h ξ dB]
  simp only [mul_sum, sum_mul]
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro ψ _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro χ _
  have hξc : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ.ne'
  field_simp [hξc]
  <;> ring

end
end ArtinMatthews
