module

public import ArtinMatthews.GiantOrderedProductTuples
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import ArtinMatthews.GiantFactorMatrix
public import ArtinMatthews.GiantOrderedProductCount
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
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


set_option backward.privateInPublic true
@[expose] public section

/-! The divisor-square moment for the actual ordered cofactor fiber.
A pair of factorizations embeds into a single tuple of matrix entries. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators

theorem giant_ordered_product_fiber_square_le (k n : ℕ) :
    (giantOrderedProductFiber k n).card^2 ≤ (giantOrderedProductFiber (k*k) n).card := by
  classical
  let S := giantOrderedProductFiber k n ×ˢ giantOrderedProductFiber k n
  let E : Fin k × Fin k ≃ Fin (k*k) := finProdFinEquiv
  have hm (p : ↥S) : ∃ a : Fin k → Fin k → ℕ, (∀ i j,0 < a i j) ∧
      (∀ i,(∏ j,a i j)=p.1.1 i) ∧ (∀ j,(∏ i,a i j)=p.1.2 j) := by
    obtain ⟨hu,hv⟩ := mem_product.mp p.2
    obtain ⟨hu₀,hu⟩ := mem_giantOrderedProductFiber.mp hu
    obtain ⟨hv₀,hv⟩ := mem_giantOrderedProductFiber.mp hv
    exact giant_exists_factor_matrix p.1.1 p.1.2 hu₀ hv₀ (hu.trans hv.symm)
  let A (p : ↥S) := Classical.choose (hm p)
  have hA (p : ↥S) : (∀ i j,0 < A p i j) ∧
      (∀ i,(∏ j,A p i j)=p.1.1 i) ∧ (∀ j,(∏ i,A p i j)=p.1.2 j) :=
    Classical.choose_spec (hm p)
  let f (p : ↥S) (i : Fin (k*k)) : ℕ := A p (E.symm i).1 (E.symm i).2
  calc
    _ = S.attach.card := by simp only [card_attach,S,card_product,pow_two]
    _ ≤ _ := by
      apply card_le_card_of_injOn f
      · intro p _
        apply mem_giantOrderedProductFiber.mpr
        refine ⟨fun i => (hA p).1 _ _,?_⟩
        calc
          (∏ i,f p i) = ∏ z : Fin k×Fin k,A p z.1 z.2 :=
            Fintype.prod_equiv E.symm _ _ (fun _ => rfl)
          _ = ∏ i,∏ j,A p i j := Fintype.prod_prod_type _
          _ = ∏ i,p.1.1 i := prod_congr rfl (fun i _ => (hA p).2.1 i)
          _ = n := (mem_giantOrderedProductFiber.mp (mem_product.mp p.2).1).2
      · intro p _ q _ he
        have hentry (i j : Fin k) : A p i j=A q i j := by
          have hh := congrFun he (E (i,j))
          simpa only [f,Equiv.symm_apply_apply] using hh
        apply Subtype.ext
        apply Prod.ext
        · funext i
          rw [← (hA p).2.1 i,← (hA q).2.1 i]
          exact prod_congr rfl (fun j _ => hentry i j)
        · funext j
          rw [← (hA p).2.2 j,← (hA q).2.2 j]
          exact prod_congr rfl (fun i _ => hentry i j)

theorem giant_ordered_product_fiber_card_sum (k X : ℕ) :
    (∑ n ∈ Ioc 0 X, ((giantOrderedProductFiber k n).card:ℝ)) =
      ((giantOrderedProductTuples k X).card:ℝ) := by
  let S := giantOrderedProductTuples k X
  let g (t : Fin k → ℕ) := ∏ i,t i
  have hmap : ∀ t ∈ S,g t ∈ Ioc 0 X := by
    intro t ht
    obtain ⟨ht₀,hcap⟩ := mem_giantOrderedProductTuples.mp ht
    exact mem_Ioc.mpr ⟨prod_pos (fun i _ => ht₀ i),hcap⟩
  calc
    _ = ∑ n ∈ Ioc 0 X,∑ _t ∈ S.filter (fun t => g t=n), (1:ℝ) := by
      apply sum_congr rfl
      intro n hn
      have he : S.filter (fun t => g t=n) = giantOrderedProductFiber k n :=
        giantOrderedProductFiber_filter (mem_Ioc.mp hn).2
      simp only [he,sum_const,nsmul_eq_mul,mul_one]
    _ = ∑ _t ∈ S,(1:ℝ) := sum_fiberwise_of_maps_to hmap _
    _ = _ := by simp only [S,sum_const,nsmul_eq_mul,mul_one]

theorem giant_ordered_product_fiber_second_moment (k X : ℕ) :
    (∑ n ∈ Ioc 0 X, ((giantOrderedProductFiber k n).card:ℝ)^2) ≤
      (X:ℝ)*(1+Real.log (X:ℝ))^(k*k) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 X, ((giantOrderedProductFiber (k*k) n).card:ℝ) := by
      apply sum_le_sum
      intro n _
      exact_mod_cast giant_ordered_product_fiber_square_le k n
    _ = ((giantOrderedProductTuples (k*k) X).card:ℝ) := giant_ordered_product_fiber_card_sum _ _
    _ ≤ _ := giant_ordered_product_count_le _ _

end ArtinMatthews
