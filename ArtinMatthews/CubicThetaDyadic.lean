module

public import ArtinMatthews.ShiftedDualDyadic
public import ArtinMatthews.CubicThetaDualSplit


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth dyadic decomposition of the actual theta Bessel dual coefficients.
All reassembly is justified by their previously proved absolute convergence. -/
noncomputable section
open Set OAI
open scoped BigOperators
namespace ArtinMatthews

def thetaDualDyadicNormalized (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (D m3 m4 q : ℕ) (d : ℕ × ℕ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (cubicThetaNebentypus (-((m3 : ℕ) : ℤ) * m4) / (q : ℂ)^2) *
      ∑' k : ℕ × ℕ, spectralDyadicCoefficient
        (shiftedDualNonzeroTerm q D m3 m4
          (thetaBesselCoeff χ W1 K1 ((q : ℝ)^2))
          (thetaBesselCoeff χ W2 K2 ((q : ℝ)^2)) k) k.1 k.2 d

theorem thetaDualDyadic_expansion_summable (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hW1 : Function.support W1 ⊆ Icc 0 B1) (hW2 : Function.support W2 ⊆ Icc 0 B2)
    (K1 K2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (D m3 m4 q : ℕ) [NeZero q] :
    Summable (fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
      spectralDyadicCoefficient (shiftedDualNonzeroTerm q D m3 m4
        (thetaBesselCoeff χ W1 K1 ((q : ℝ)^2))
        (thetaBesselCoeff χ W2 K2 ((q : ℝ)^2)) z.1) z.1.1 z.1.2 z.2) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  exact shiftedDualNonzero_dyadic_summable q D m3 m4 _ _
    (thetaBesselCoeff_summable χ W1 B1 hB1 hW1 K1 _ hK1 (by positivity))
    (thetaBesselCoeff_summable χ W2 B2 hB2 hW2 K2 _ hK2 (by positivity))
    (thetaBesselCoeff_zero χ W1 K1 _) (thetaBesselCoeff_zero χ W2 K2 _)

theorem thetaDualDyadic_summable (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hW1 : Function.support W1 ⊆ Icc 0 B1) (hW2 : Function.support W2 ⊆ Icc 0 B2)
    (K1 K2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (D m3 m4 q : ℕ) :
    Summable (thetaDualDyadicNormalized χ W1 W2 K1 K2 D m3 m4 q) := by
  change Summable (fun d : ℕ × ℕ => thetaDualDyadicNormalized χ W1 W2 K1 K2 D m3 m4 q d)
  by_cases hq : q = 0
  · simp [thetaDualDyadicNormalized,hq]
  · let : NeZero q := ⟨hq⟩
    simp only [thetaDualDyadicNormalized,dite_eq_right hq]
    exact (thetaDualDyadic_expansion_summable χ W1 W2 B1 B2 hB1 hB2 hW1 hW2
      K1 K2 hK1 hK2 D m3 m4 q).prod_symm.prod.mul_left _

theorem thetaDualNonzeroNormalized_eq_dyadic (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hW1 : Function.support W1 ⊆ Icc 0 B1) (hW2 : Function.support W2 ⊆ Icc 0 B2)
    (K1 K2 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (D m3 m4 q : ℕ) :
    thetaDualNonzeroNormalized χ W1 W2 K1 K2 D m3 m4 q =
      ∑' d, thetaDualDyadicNormalized χ W1 W2 K1 K2 D m3 m4 q d := by
  by_cases hq : q = 0
  · simp [thetaDualNonzeroNormalized,thetaDualDyadicNormalized,hq]
  · let : NeZero q := ⟨hq⟩
    have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    simp only [thetaDualNonzeroNormalized,thetaDualDyadicNormalized,dite_eq_right hq]
    rw [tsum_mul_left]
    congr 1
    exact shiftedDualNonzero_dyadic_reassembly q D m3 m4 _ _
      (thetaBesselCoeff_summable χ W1 B1 hB1 hW1 K1 _ hK1 (by positivity))
      (thetaBesselCoeff_summable χ W2 B2 hB2 hW2 K2 _ hK2 (by positivity))
      (thetaBesselCoeff_zero χ W1 K1 _) (thetaBesselCoeff_zero χ W2 K2 _)

end ArtinMatthews
