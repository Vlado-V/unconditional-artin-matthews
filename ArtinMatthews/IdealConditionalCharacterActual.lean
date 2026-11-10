module

public import ArtinMatthews.IdealConditionalCharacterFrame
public import ArtinMatthews.MarkedBonferroniTail
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual retained source cells have character-frame norm at most two.
The off-diagonal estimate is supplied by the proved prime cancellation. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem idealConditionalCharacterFrame_actual (a c d X v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hX : 0 ≤ X) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (Q : ℕ), (Q : ℝ) ≤ L^a →
        ∀ (P : I → Finset ℕ), (∀ i p, p ∈ P i → p.Prime) →
        (∀ i, 0 < bandReciprocalMass (P i)) →
        (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        ∀ i : I, IdealPrimeInterval (P i) → v₀ ≤ bandReciprocalMass (P i) →
        ∀ (h : ℝ), 0 < h → ∀ j : ℤ, L^(-X) ≤ idealLogCellMass P h j →
        ∀ f : IdealSelectedLabels P → ℂ,
          idealFrameEnergy (idealCellConditionalMass P h j)
            (idealConditionalCharacterFrame P Q h j f) ≤
              4 * idealFrameEnergy (idealCellConditionalMass P h j) f := by
  have hexp := (rpow_mul_exp_neg_rpow_tendsto a hc (by norm_num : (0 : ℝ) < 1)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [idealCharacterCellGram_offDiagonal (I := I) a c d (2*a+X) v₀
    ha hc hd (by positivity) hv₀, hexp, eventually_gt_atTop (0 : ℝ)] with L hoff hexp hL
  intro Q hQ P hP hV hbounds i hinterval hVlo h hh j hret f
  have hlarge : ∀ k p, p ∈ P k → Q < p := by
    intro k p hp
    have he : L^a < Real.exp (L^c) := by
      apply (div_lt_one (Real.exp_pos _)).mp
      simpa only [neg_one_mul, Real.exp_neg, div_eq_mul_inv] using hexp
    have hb : (Q : ℝ) < p := hQ.trans_lt (he.trans_le (hbounds k p hp).1)
    exact_mod_cast hb
  have hm : 0 < idealLogCellMass P h j := (Real.rpow_pos_of_pos hL (-X)).trans_le hret
  have hQ2 : (Q : ℝ)^2 ≤ L^(2*a) := by
    calc
      _ ≤ (L^a)^2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
      _ = _ := by
        rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
        congr 1
        ring
  have hbudget : (Q : ℝ)^2 * L^(-(2*a+X)) ≤ L^(-X) := by
    calc
      _ ≤ L^(2*a) * L^(-(2*a+X)) :=
        mul_le_mul_of_nonneg_right hQ2 (Real.rpow_nonneg hL.le _)
      _ = _ := by rw [← Real.rpow_add hL]; congr 1; ring
  have hratio : (Q : ℝ)^2 * (L^(-(2*a+X)) / idealLogCellMass P h j) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_one₀ hm).mpr (hbudget.trans hret)
  have hframe := idealConditionalCharacterFrame_energy_le P hV Q h j hP hlarge
    (ε := L^(-(2*a+X))) (Real.rpow_nonneg hL.le _) hm
    (fun χ ψ hne => hoff Q hQ χ ψ hne P hP hV i hinterval (hbounds i) hVlo h hh j) f
  have hnonneg : 0 ≤ (Q : ℝ)^2 * (L^(-(2*a+X)) / idealLogCellMass P h j) := by positivity
  have hsquare : (1 + (Q : ℝ)^2 * (L^(-(2*a+X)) / idealLogCellMass P h j))^2 ≤ 4 := by
    nlinarith
  exact hframe.trans (mul_le_mul_of_nonneg_right hsquare
    (idealFrameEnergy_nonneg _ (idealCellConditionalMass_nonneg P hV h j) f))

end
end ArtinMatthews
