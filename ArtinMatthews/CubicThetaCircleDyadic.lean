module

public import ArtinMatthews.CubicThetaDyadic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact dyadic reassembly across the actual finite set of circle moduli,
with its original smooth weights and normalization. -/
noncomputable section
open Set OAI
open scoped BigOperators
namespace ArtinMatthews

def thetaDualDyadicCircleBlock (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (D m3 m4 F r L : ℕ) (d : ℕ × ℕ) : ℂ :=
  (∑ q ∈ circleModuli F r L, (circleSmoothWeight L q : ℂ) *
    thetaDualDyadicNormalized χ W1 W2 K1 K2 D m3 m4 q d) /
      (circleNormalizer (circleModuli F r L) (circleSmoothWeight L) : ℂ)

theorem thetaDualDyadicCircleBlock_summable (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hW1 : Function.support W1 ⊆ Icc 0 B1) (hW2 : Function.support W2 ⊆ Icc 0 B2)
    (K1 K2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (D m3 m4 F r L : ℕ) :
    Summable (thetaDualDyadicCircleBlock χ W1 W2 K1 K2 D m3 m4 F r L) := by
  change Summable (fun d => thetaDualDyadicCircleBlock χ W1 W2 K1 K2 D m3 m4 F r L d)
  unfold thetaDualDyadicCircleBlock
  apply Summable.div_const
  apply summable_sum
  intro q _
  exact (thetaDualDyadic_summable χ W1 W2 B1 B2 hB1 hB2 hW1 hW2
    K1 K2 hK1 hK2 D m3 m4 q).mul_left _

theorem thetaDualNonzeroCircleAverage_eq_dyadic (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hW1 : Function.support W1 ⊆ Icc 0 B1) (hW2 : Function.support W2 ⊆ Icc 0 B2)
    (K1 K2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (D m3 m4 F r L : ℕ) :
    thetaDualNonzeroCircleAverage χ W1 W2 K1 K2 D m3 m4 F r L =
      ∑' d, thetaDualDyadicCircleBlock χ W1 W2 K1 K2 D m3 m4 F r L d := by
  unfold thetaDualNonzeroCircleAverage thetaDualDyadicCircleBlock
  rw [tsum_div_const]
  congr 1
  rw [Summable.tsum_finsetSum (fun q _ =>
    (thetaDualDyadic_summable χ W1 W2 B1 B2 hB1 hB2 hW1 hW2
      K1 K2 hK1 hK2 D m3 m4 q).mul_left (circleSmoothWeight L q : ℂ))]
  apply Finset.sum_congr rfl
  intro q _
  rw [tsum_mul_left,thetaDualNonzeroNormalized_eq_dyadic χ W1 W2 B1 B2
    hB1 hB2 hW1 hW2 K1 K2 hK1 hK2]

end ArtinMatthews
