module

public import ArtinMatthews.FixedURootWeightedBoxes
public import ArtinMatthews.FixedURootBoxMain
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The unoptimized arithmetic root-count error under smooth weights.
The modulus, both coordinate scales and the complete Euler remainder are
retained before imposing the eventual subpower-modulus range. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def fixedURootExplicitError (K : ℝ) (N S : ℕ) (A B α β C D : ℝ) : ℝ :=
  K*B^(99/100 : ℝ)*(S : ℝ)^2*(2+(D-C)/A)*((B-A)/(S : ℝ)+1) +
    ((β-α)*(D-C)/(S : ℝ)^2)*(2+Real.log N)

theorem fixedURootMatrixBox_tail_explicit_error : ∃ K : ℝ, 0 < K ∧
    ∀ (N S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
      (A B α β C D t s : ℝ) (lcR rcR : Bool),
      0 < N → Squarefree S → 1 ≤ A → A ≤ B → B ≤ N →
      0 ≤ α → α ≤ β → β ≤ 1 → C ≤ D →
      t ∈ Set.Icc A B → s ∈ Set.Icc C D →
      |((fixedURootMatrixBoxPoints g₀ t B α β s D true true lcR rcR true true).card : ℝ) -
        ((B-t)*(β-α)*(D-s))/((riemannZeta 2).re *
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
        fixedURootExplicitError K N S A B α β C D := by
  obtain ⟨K,hK,hcount⟩ := fixedURootBox_card_error
  refine ⟨K,hK,?_⟩
  intro N S g₀ A B α β C D t s lcR rcR hN hS hA hAB hBN hα hαβ hβ hCD ht hs
  let : NeZero S := ⟨hS.ne_zero⟩
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have ht0 : 0 < t := hA0.trans_le ht.1
  have hB0 : 0 < B := hA0.trans_le hAB
  have hS0 : (0 : ℝ) < S := by exact_mod_cast Nat.pos_of_ne_zero hS.ne_zero
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hc := hcount N S (fixedURootMatrixEntry g₀ 0 0) (fixedURootMatrixEntry g₀ 0 1)
    (fixedURootMatrixEntry g₀ 1 0) (fixedURootMatrixEntry g₀ 1 1)
    t B α β s D true true lcR rcR true true hN hS (fixedURootMatrixEntry_det g₀)
    (hA.trans ht.1) ht.2 hBN hα hαβ hβ hs.2
  change |((fixedURootMatrixBoxPoints g₀ t B α β s D true true lcR rcR true true).card : ℝ) - _| ≤ _ at hc
  apply hc.trans
  have hfrac : (D-s)/t ≤ (D-C)/A :=
    (div_le_div_of_nonneg_right (sub_le_sub_left hs.1 D) ht0.le).trans
      (div_le_div_of_nonneg_left (sub_nonneg.mpr hCD) hA0 ht.1)
  have hwidth : (B-t)/(S : ℝ)+1 ≤ (B-A)/(S : ℝ)+1 :=
    add_le_add (div_le_div_of_nonneg_right (sub_le_sub_left ht.1 B) hS0.le) le_rfl
  unfold fixedURootExplicitError
  apply add_le_add
  · have hnon : 0 ≤ K*B^(99/100 : ℝ)*(S : ℝ)^2 := by positivity
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hfrac) hnon
    · exact hwidth
    · exact add_nonneg (div_nonneg (sub_nonneg.mpr ht.2) hS0.le) zero_le_one
    · exact mul_nonneg hnon (add_nonneg (by norm_num)
        (div_nonneg (sub_nonneg.mpr hCD) hA0.le))
  · apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ 2+Real.log (N : ℝ))
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hs.1 D) (sub_nonneg.mpr hαβ))
      (sq_nonneg _)

/-- Smooth weights against the fully explicit arithmetic error, with no
asymptotic modulus or coordinate-regime restriction. -/
theorem fixedURootWeightedSum_explicit_error : ∃ K : ℝ, 0 < K ∧
    ∀ (N S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
      (A B α β C D : ℝ) (lcR rcR : Bool) (f g : ℝ → ℂ),
      0 < N → Squarefree S → 1 ≤ A → A ≤ B → B ≤ N →
      0 ≤ α → α ≤ β → β ≤ 1 → C ≤ D →
      Differentiable ℝ f → Continuous (deriv f) →
      Differentiable ℝ g → Continuous (deriv g) →
      ‖fixedURootWeightedSum g₀ A B α β C D lcR rcR f g -
        fixedURootWeightedMain S A B α β C D f g‖ ≤
        fixedURootExplicitError K N S A B α β C D *
          rootWeightVariation f A B*rootWeightVariation g C D := by
  obtain ⟨K,hK,hcount⟩ := fixedURootMatrixBox_tail_explicit_error
  refine ⟨K,hK,?_⟩
  intro N S g₀ A B α β C D lcR rcR f g hN hS hA hAB hBN hα hαβ hβ hCD hf hdf hg hdg
  exact fixedURootWeightedSum_error_of_counts g₀ A B α β C D lcR rcR f g hAB hCD hf hdf hg hdg
    (fun t ht s hs => hcount N S g₀ A B α β C D t s lcR rcR hN hS hA hAB hBN hα hαβ hβ hCD ht hs)

end ArtinMatthews
