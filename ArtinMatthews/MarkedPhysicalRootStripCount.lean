module

public import ArtinMatthews.MarkedPhysicalRootStripGeometry
public import ArtinMatthews.FixedURootFullPowerSaving
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

/-! Actual root counts with simultaneous source-arc and target-strip tests.
The zero/empty cases are exact and the root error is the proved rectangle
error, uniformly in the integer target coordinates. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalRootStripMain (S : ℕ) (A B α β C D : ℝ) (z : ℤ × ℤ) : ℝ :=
  if markedPhysicalStripArcActive z α β then
    ((B-A)*(markedPhysicalStripArcUpper z β-markedPhysicalStripArcLower z α)*(D-C)) /
      ((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))
  else 0

theorem markedPhysicalRootStrip_count_error {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B α β C D : ℝ) (z : ℤ × ℤ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U →
        0 ≤ α → β ≤ 1 → V ≤ C → C ≤ D → D ≤ 2*V →
        |((markedPhysicalRootStripPoints g₀ A B α β C D z).card : ℝ) -
          markedPhysicalRootStripMain S A B α β C D z| ≤ E*U*V*x^(-δ/1000) := by
  obtain ⟨E,hE,hcount⟩ := fixedURootMatrixBox_uniform_power_saving hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro S g₀ U V A B α β C D z hU hV hS hSr hUA hAB hB hα hβ hVC hCD hD
  have hUp : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) δ).trans_le hV
  have hA1 : 1 < A := ((Real.one_lt_rpow hx1 hδ).trans_le hU).trans_le hUA
  rw [markedPhysicalRootStripPoints_eq g₀ A B α β C D z hA1 hα hβ,
    markedPhysicalRootStripMain]
  by_cases ha : markedPhysicalStripArcActive z α β
  · rw [ite_eq_left ha, ite_eq_left ha]
    have hb := markedPhysicalStripArc_bounds z hα hβ ha
    exact hx S g₀ U V A B (markedPhysicalStripArcLower z α) (markedPhysicalStripArcUpper z β)
      C D true true true true true true hU hV hS hSr hUA hAB hB hb.1 hb.2.1 hb.2.2 hVC hCD hD
  · rw [ite_eq_right ha, ite_eq_right ha, Finset.card_empty, Nat.cast_zero, sub_self, abs_zero]
    positivity

/-- Weighted sums of actual strip/arc root counts, with one error per
coefficient and the literal UV normalization retained. -/
theorem markedPhysicalRootStrip_sum_error {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type*} (I : Finset ι) (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
        (U V A B C D : ℝ) (α β : ι → ℝ) (z : ι → ℤ × ℤ) (c : ι → ℂ),
        x^δ ≤ U → x^δ ≤ V → Squarefree S →
        (S : ℝ) ≤ Real.exp (M*(Real.log x)^(49/50 : ℝ)) →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
        (∀ i ∈ I, 0 ≤ α i ∧ β i ≤ 1) →
        ‖∑ i ∈ I, c i *
          (((markedPhysicalRootStripPoints g₀ A B (α i) (β i) C D (z i)).card : ℂ) -
            (markedPhysicalRootStripMain S A B (α i) (β i) C D (z i) : ℂ))‖ / (U*V) ≤
          E*x^(-δ/1000)*∑ i ∈ I, ‖c i‖ := by
  obtain ⟨E,hE,hcount⟩ := markedPhysicalRootStrip_count_error hδ M
  refine ⟨E,hE,?_⟩
  filter_upwards [hcount, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro ι I S g₀ U V A B C D α β z c hU hV hS hSr hUA hAB hB hVC hCD hD hα
  have hUp : 0 < U := (Real.rpow_pos_of_pos hx0 δ).trans_le hU
  have hVp : 0 < V := (Real.rpow_pos_of_pos hx0 δ).trans_le hV
  apply (div_le_iff₀ (mul_pos hUp hVp)).mpr
  calc
    _ ≤ ∑ i ∈ I, ‖c i‖ *
        ‖((markedPhysicalRootStripPoints g₀ A B (α i) (β i) C D (z i)).card : ℂ) -
          (markedPhysicalRootStripMain S A B (α i) (β i) C D (z i) : ℂ)‖ := by
      simpa only [norm_mul] using norm_sum_le I (fun i => c i *
        (((markedPhysicalRootStripPoints g₀ A B (α i) (β i) C D (z i)).card : ℂ) -
          (markedPhysicalRootStripMain S A B (α i) (β i) C D (z i) : ℂ)))
    _ ≤ ∑ i ∈ I, ‖c i‖*(E*U*V*x^(-δ/1000)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hx S g₀ U V A B (α i) (β i) C D (z i) hU hV hS hSr hUA hAB hB
        (hα i hi).1 (hα i hi).2 hVC hCD hD
    _ = _ := by rw [← Finset.sum_mul]; ring

end ArtinMatthews
