module

public import ArtinMatthews.SourceKPRationalHeight
public import Mathlib.Analysis.Normed.Ring.InfiniteSum


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute summability of a concrete height majorant over the full
rational field. The proof uses the actual denominator and Minkowski
integer lattice, without a rational-point counting hypothesis. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Filter
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem sourceKPRationalHeightLatticePoint_ne_zero {x : K} (hx : x ≠ 0) :
    sourceKPRationalHeightLatticePoint K x ≠ 0 := by
  intro h
  have he := congrArg (fun a : mixedEmbedding.integerLattice K => a.val) h
  change mixedEmbedding K ((sourceKPRationalHeightDenominator K x : K) * x) = 0 at he
  have hzero : mixedEmbedding K ((sourceKPRationalHeightDenominator K x : K) * x) =
      mixedEmbedding K 0 := by simpa only [map_zero] using he
  have hp := mixedEmbedding_injective K hzero
  exact (mul_ne_zero (Nat.cast_ne_zero.mpr (sourceKPRationalHeightDenominator_spec K x).1) hx) hp

theorem sourceKPRationalHeight_inv_pow_bound (k : ℕ) {x : K} (hx : x ≠ 0) :
    (Height.mulHeight₁ x ^ (3*k))⁻¹ ≤
      ((sourceKPRationalHeightDenominator K x : ℝ)^k)⁻¹ *
        (‖(sourceKPRationalHeightLatticePoint K x).val‖^k)⁻¹ := by
  have hn : 0 < (sourceKPRationalHeightDenominator K x : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (sourceKPRationalHeightDenominator_spec K x).1)
  have ha : 0 < ‖(sourceKPRationalHeightLatticePoint K x).val‖ := by
    apply norm_pos_iff.mpr
    intro h
    exact sourceKPRationalHeightLatticePoint_ne_zero K hx (Subtype.ext h)
  have hbound : (sourceKPRationalHeightDenominator K x : ℝ)^k *
      ‖(sourceKPRationalHeightLatticePoint K x).val‖^k ≤ Height.mulHeight₁ x ^ (3*k) := by
    calc
      _ ≤ Height.mulHeight₁ x ^ k * (Height.mulHeight₁ x ^ 2)^k :=
        mul_le_mul
          (pow_le_pow_left₀ hn.le (sourceKPRationalHeightDenominator_spec K x).2.1 k)
          (pow_le_pow_left₀ (norm_nonneg _) (sourceKPRationalHeightLatticePoint_norm K x) k)
          (pow_nonneg (norm_nonneg _) k) (pow_nonneg (Height.mulHeight₁_nonneg x) k)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  calc
    _ ≤ ((sourceKPRationalHeightDenominator K x : ℝ)^k *
        ‖(sourceKPRationalHeightLatticePoint K x).val‖^k)⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (mul_pos (pow_pos hn k) (pow_pos ha k)) hbound
    _ = _ := mul_inv _ _

theorem sourceKPRationalHeight_inv_pow_summable (k : ℕ)
    (hk : 1 < k) (hdegree : Module.finrank ℚ K < k) :
    Summable (fun x : K => (Height.mulHeight₁ x ^ (3*k))⁻¹) := by
  have hn : Summable (fun n : ℕ => ((n : ℝ)^k)⁻¹) := Real.summable_nat_pow_inv.mpr hk
  have hdim : Module.finrank ℤ (mixedEmbedding.integerLattice K) = Module.finrank ℚ K := by
    rw [ZLattice.rank ℝ, mixedEmbedding.finrank]
  have hl := ZLattice.summable_norm_rpow (mixedEmbedding.integerLattice K) (-(k : ℝ))
    (show -(k : ℝ) < -(Module.finrank ℤ (mixedEmbedding.integerLattice K) : ℝ) by
      rw [hdim]
      exact neg_lt_neg (by exact_mod_cast hdegree))
  have hl' : Summable (fun a : mixedEmbedding.integerLattice K => (‖a.val‖^k)⁻¹) := by
    simpa only [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← Submodule.norm_coe] using hl
  have hpair := summable_mul_of_summable_norm hn.norm hl'.norm
  have hcoord := hpair.comp_injective (sourceKPRationalHeightCoordinates_injective K)
  apply hcoord.of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0 : K)] with x hx
  change ‖(Height.mulHeight₁ x ^ (3*k))⁻¹‖ ≤
    ((sourceKPRationalHeightDenominator K x : ℝ)^k)⁻¹ *
      (‖(sourceKPRationalHeightLatticePoint K x).val‖^k)⁻¹
  rw [Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (Height.mulHeight₁_nonneg x) (3*k)))]
  exact sourceKPRationalHeight_inv_pow_bound K k hx

theorem sourceKPRationalHeight_degree_majorant_summable :
    Summable (fun x : K => (Height.mulHeight₁ x ^ (3*(Module.finrank ℚ K+1)))⁻¹) :=
  sourceKPRationalHeight_inv_pow_summable K (Module.finrank ℚ K+1)
    (by have hd : 0 < Module.finrank ℚ K := Module.finrank_pos; omega) (Nat.lt_succ_self _)

end
end ArtinMatthews
