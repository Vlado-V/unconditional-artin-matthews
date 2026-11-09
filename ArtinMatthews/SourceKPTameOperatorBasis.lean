module

public import ArtinMatthews.SourceKPTameOperator


set_option backward.privateInPublic true
@[expose] public section

/-! Exact action of the tame torus operator on the Jacquet coordinate
basis, and the scalar action when the valuation is divisible by three. -/

namespace ArtinMatthews
noncomputable section

theorem sourceKPTameOperator_basis (Q : ℝ) (z u : ℂˣ) (j : ℤ) (i : ZMod 3) :
    sourceKPTameOperator Q z u j (sourceJacquetBasis i) =
      ((z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) *
        (sourceKPCubicPower (A := ℂˣ) u (-(j : ZMod 3) - 2 * i) : ℂ)) •
        sourceJacquetBasis (i + (j : ZMod 3)) := by
  funext t
  let J : ZMod 3 := j
  change (z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) *
      (sourceKPCubicPower (A := ℂˣ) u (J - 2 * t) : ℂ) * sourceJacquetBasis i (t - J) =
    ((z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) *
      (sourceKPCubicPower (A := ℂˣ) u (-J - 2 * i) : ℂ)) * sourceJacquetBasis (i + J) t
  have he : t - J = i ↔ t = i + J := sub_eq_iff_eq_add
  by_cases h : t = i + J
  · have h0 := he.mpr h
    have hp : J - 2 * t = -J - 2 * i := by
      rw [h, mul_add, two_mul J]
      abel
    rw [hp, h0, h]
    simp only [sourceJacquetBasis, Pi.single_eq_same]
  · have h0 : t - J ≠ i := fun ht => h (he.mp ht)
    simp only [sourceJacquetBasis, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h, mul_zero]

theorem sourceKPTameOperator_scalar (Q : ℝ) (z : ℂˣ) (j : ℤ) (hj : (j : ZMod 3) = 0)
    (f : ZMod 3 → ℂ) :
    sourceKPTameOperator Q z 1 j f = ((z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6)) • f := by
  funext i
  change (z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) *
      (sourceKPCubicPower (A := ℂˣ) 1 ((j : ZMod 3) - 2 * i) : ℂ) * f (i - (j : ZMod 3)) =
    ((z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6)) * f i
  rw [sourceKPCubicPower_one, Units.val_one, mul_one, hj]
  exact congrArg (fun t : ZMod 3 => (z : ℂ) * sourceJacquetScale Q ((j : ℝ) / 6) * f t) (sub_zero i)

end
end ArtinMatthews
