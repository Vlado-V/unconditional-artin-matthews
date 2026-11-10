module

public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A direct majorant for rational summation over an arbitrary number
field. The actual multiplicative height controls a nonzero integral
denominator and its numerator in the Minkowski integer lattice. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem sourceKPInfinitePlace_le_height (v : InfinitePlace K) (x : K) :
    v x ≤ Height.mulHeight₁ x := by
  classical
  have hv : v x ≤ max (v x) 1 ^ v.mult :=
    (le_max_left _ _).trans (le_self_pow₀ (le_max_right _ _) v.mult_ne_zero)
  have hp : max (v x) 1 ^ v.mult ≤ ∏ w : InfinitePlace K, max (w x) 1 ^ w.mult := by
    have hrest : 1 ≤ ∏ w ∈ Finset.univ.erase v, max (w x) 1 ^ w.mult :=
      Finset.one_le_prod₀ (fun w _ => one_le_pow₀ (le_max_right _ _))
    calc
      _ ≤ (∏ w ∈ Finset.univ.erase v, max (w x) 1 ^ w.mult) * (max (v x) 1 ^ v.mult) :=
        le_mul_of_one_le_left (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _) hrest
      _ = _ := Finset.prod_erase_mul _ _ (Finset.mem_univ v)
  rw [NumberField.mulHeight₁_eq]
  exact hv.trans (hp.trans (le_mul_of_one_le_right
    (Finset.prod_nonneg (fun _ _ => pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _))
    (one_le_finprod (fun _ => le_max_right _ _))))

theorem sourceKPMixedEmbedding_norm_le_height (x : K) :
    ‖mixedEmbedding K x‖ ≤ Height.mulHeight₁ x := by
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  apply Finset.sup'_le
  intro v _
  rw [mixedEmbedding.normAtPlace_apply]
  exact sourceKPInfinitePlace_le_height K v x

def sourceKPRationalHeightDenominator (x : K) : ℕ :=
  Classical.choose (NumberField.exists_nat_le_mulHeight₁ x)

theorem sourceKPRationalHeightDenominator_spec (x : K) :
    sourceKPRationalHeightDenominator K x ≠ 0 ∧
      (sourceKPRationalHeightDenominator K x : ℝ) ≤ Height.mulHeight₁ x ∧
      IsIntegral ℤ ((sourceKPRationalHeightDenominator K x : K) * x) :=
  Classical.choose_spec (NumberField.exists_nat_le_mulHeight₁ x)

def sourceKPRationalHeightLatticePoint (x : K) : mixedEmbedding.integerLattice K :=
  ⟨mixedEmbedding K ((sourceKPRationalHeightDenominator K x : K) * x),
    ⟨⟨(sourceKPRationalHeightDenominator K x : K) * x,
      (sourceKPRationalHeightDenominator_spec K x).2.2⟩, rfl⟩⟩

theorem sourceKPRationalHeightLatticePoint_norm (x : K) :
    ‖(sourceKPRationalHeightLatticePoint K x).val‖ ≤ Height.mulHeight₁ x ^ 2 := by
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  apply Finset.sup'_le
  intro v _
  change mixedEmbedding.normAtPlace v
    (mixedEmbedding K ((sourceKPRationalHeightDenominator K x : K) * x)) ≤ _
  rw [mixedEmbedding.normAtPlace_apply, map_mul, InfinitePlace.map_natCast]
  simpa only [pow_two] using mul_le_mul
    (sourceKPRationalHeightDenominator_spec K x).2.1
    (sourceKPInfinitePlace_le_height K v x) (apply_nonneg v x) (Height.mulHeight₁_nonneg x)

theorem sourceKPRationalHeightCoordinates_injective : Function.Injective
    (fun x : K => (sourceKPRationalHeightDenominator K x, sourceKPRationalHeightLatticePoint K x)) := by
  intro x y h
  have hn := congrArg Prod.fst h
  change sourceKPRationalHeightDenominator K x = sourceKPRationalHeightDenominator K y at hn
  have ha := congrArg (fun p : ℕ × mixedEmbedding.integerLattice K => p.2.val) h
  have hxy := mixedEmbedding_injective K ha
  change (sourceKPRationalHeightDenominator K x : K) * x =
    (sourceKPRationalHeightDenominator K y : K) * y at hxy
  rw [← hn] at hxy
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (sourceKPRationalHeightDenominator_spec K x).1) hxy

end
end ArtinMatthews
