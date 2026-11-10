module

public import ArtinMatthews.GiantMixedSlotCofactor
public import ArtinMatthews.GiantOrderedProductMoment
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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

/-! The reciprocal second moment pays the literal hyperbola row length
when the cofactor coefficient is truncated. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giant_ordered_product_fiber_reciprocal_sum_le (k X : ℕ) :
    (∑ n ∈ Ioc 0 X, ((giantOrderedProductFiber k n).card:ℝ)/(n:ℝ)) ≤
      (1+Real.log (X:ℝ))^k := by
  let S := giantOrderedProductTuples k X
  let g (t : Fin k → ℕ) := ∏ i,t i
  let F (t : Fin k → ℕ) := (g t:ℝ)⁻¹
  have hmap : ∀ t ∈ S,g t ∈ Ioc 0 X := by
    intro t ht
    obtain ⟨hpos,hcap⟩ := mem_giantOrderedProductTuples.mp ht
    exact mem_Ioc.mpr ⟨prod_pos (fun i _ => hpos i),hcap⟩
  have hH : (∑ n ∈ Ioc 0 X,(n:ℝ)⁻¹) ≤ 1+Real.log (X:ℝ) := by
    have he : Ioc 0 X = Icc 1 X := by
      ext n
      simp only [mem_Ioc,mem_Icc]
      omega
    rw [he]
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      using harmonic_le_one_add_log X
  calc
    _ = ∑ n ∈ Ioc 0 X,∑ t ∈ S.filter (fun t => g t=n), F t := by
      apply sum_congr rfl
      intro n hn
      have hf : S.filter (fun t => g t=n) = giantOrderedProductFiber k n :=
        giantOrderedProductFiber_filter (mem_Ioc.mp hn).2
      calc
        _ = ∑ _t ∈ giantOrderedProductFiber k n,(n:ℝ)⁻¹ := by
          simp only [sum_const,nsmul_eq_mul,div_eq_mul_inv]
        _ = _ := by
          rw [hf]
          apply sum_congr rfl
          intro t ht
          dsimp only [F,g]
          rw [(mem_giantOrderedProductFiber.mp ht).2]
    _ = ∑ t ∈ S,F t := sum_fiberwise_of_maps_to hmap F
    _ ≤ ∑ t ∈ Fintype.piFinset (fun _ : Fin k => Ioc 0 X), F t :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by dsimp [F]; positivity)
    _ = (∑ n ∈ Ioc 0 X,(n:ℝ)⁻¹)^k := by
      simp only [F,g,Nat.cast_prod,← prod_inv_distrib]
      exact (sum_pow' (Ioc 0 X) (fun n : ℕ => (n:ℝ)⁻¹) k).symm
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hH k

theorem giant_ordered_product_fiber_reciprocal_second_moment (k X : ℕ) :
    (∑ n ∈ Ioc 0 X, ((giantOrderedProductFiber k n).card:ℝ)^2/(n:ℝ)) ≤
      (1+Real.log (X:ℝ))^(k*k) := by
  apply le_trans _ (giant_ordered_product_fiber_reciprocal_sum_le (k*k) X)
  apply sum_le_sum
  intro n _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast giant_ordered_product_fiber_square_le k n

def giantCofactorTruncate (R : ℝ) (β : ℕ → ℂ) (n : ℕ) : ℂ :=
  if ‖β n‖ ≤ R then β n else 0

theorem giantCofactorTruncate_norm_le {R : ℝ} (hR : 0 ≤ R) (β : ℕ → ℂ) (n : ℕ) :
    ‖giantCofactorTruncate R β n‖ ≤ R := by
  unfold giantCofactorTruncate
  split_ifs with h
  · exact h
  · simpa only [norm_zero] using hR

theorem giantCofactorTruncate_ne_zero {R : ℝ} {β : ℕ → ℂ} {n : ℕ}
    (h : giantCofactorTruncate R β n ≠ 0) : β n ≠ 0 := by
  intro hzero
  exact h (by simp [giantCofactorTruncate,hzero])

theorem giant_mixed_cofactor_tail_le {k : ℕ} (i : Fin (k+1)) (W z : ℝ) (X : ℕ)
    {R : ℝ} (hR : 0 < R) (hprime : ∀ m, ‖giantPrimeSlotCoefficient z m‖ ≤ 1)
    (hrough : ∀ m, ‖giantRoughSlotCoefficient W z m‖ ≤ 1) :
    let β := giantMixedCofactorCoefficient i W z
    (∑ n ∈ Ioc 0 X, ‖β n-giantCofactorTruncate R β n‖/(n:ℝ)) ≤
      (1+Real.log (X:ℝ))^(k*k)/R := by
  let β := giantMixedCofactorCoefficient i W z
  have hpoint (n : ℕ) : ‖β n-giantCofactorTruncate R β n‖ ≤ ‖β n‖^2/R := by
    unfold giantCofactorTruncate
    split_ifs with h
    · rw [sub_self,norm_zero]
      positivity
    · rw [sub_zero]
      apply (le_div_iff₀ hR).mpr
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (le_of_not_ge h) (norm_nonneg _)
  have hnorm (n : ℕ) : ‖β n‖ ≤ ((giantOrderedProductFiber k n).card:ℝ) := by
    simpa only [one_pow,mul_one,β] using
      giantMixedCofactorCoefficient_norm_le i W z n 1 hprime hrough
  change (∑ n ∈ Ioc 0 X, ‖β n-giantCofactorTruncate R β n‖/(n:ℝ)) ≤ _
  calc
    _ ≤ ∑ n ∈ Ioc 0 X, ((giantOrderedProductFiber k n).card:ℝ)^2/R/(n:ℝ) := by
      apply sum_le_sum
      intro n _
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact (hpoint n).trans (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2) hR.le)
    _ = (∑ n ∈ Ioc 0 X, ((giantOrderedProductFiber k n).card:ℝ)^2/(n:ℝ))/R := by
      rw [sum_div]
      apply sum_congr rfl
      intro n _
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (giant_ordered_product_fiber_reciprocal_second_moment k X) hR.le

end
end ArtinMatthews
