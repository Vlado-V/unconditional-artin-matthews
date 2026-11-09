module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.MeanInequalities


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted finite power means with the total weight, rather than the
cardinality, as normalization. This is the scalar spectral-Hölder input. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

theorem markedWeightedPowerMean {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    (∑ i, w i*x i)^(k+1) ≤ (∑ i, w i)^k * ∑ i, w i*x i^(k+1) := by
  let W := ∑ i, w i
  have hW : 0 ≤ W := Finset.sum_nonneg (fun i _ => hw i)
  by_cases hW0 : W=0
  · have hzero : ∀ i, w i=0 := by
      have he : (∑ i, w i)=0 := hW0
      exact fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw j)).mp he i (Finset.mem_univ i)
    simp only [hzero,zero_mul,Finset.sum_const_zero,zero_pow (Nat.succ_ne_zero k),mul_zero]
    exact le_rfl
  have hWp : 0 < W := lt_of_le_of_ne hW (Ne.symm hW0)
  have hmass : ∑ i, w i/W = 1 := by rw [← Finset.sum_div]; exact div_self hW0
  have h := (convexOn_pow (𝕜 := ℝ) (k+1)).map_sum_le
    (t := Finset.univ) (w := fun i => w i/W) (p := x)
    (fun i _ => div_nonneg (hw i) hW) hmass (fun i _ => hx i)
  have hs (y : ι → ℝ) : (∑ i, (w i/W)*y i) = (∑ i, w i*y i)/W := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  simp only [smul_eq_mul] at h
  rw [hs,hs,div_pow] at h
  have hh := (div_le_iff₀ (pow_pos hWp (k+1))).mp h
  calc
    _ ≤ ((∑ i, w i*x i^(k+1))/W) * W^(k+1) := hh
    _ = W^k * ∑ i, w i*x i^(k+1) := by rw [pow_succ]; field_simp

end
end ArtinMatthews
