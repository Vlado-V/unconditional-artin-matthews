module

public import ArtinMatthews.CubicThetaDualZero
public import ArtinMatthews.ShiftedDualZeroScale
public import ArtinMatthews.ShiftedVoronoiCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! The exact denominator and nebentypus normalization of the zero dual
frequency leaves only a subpower growth in the modulus. -/

noncomputable section
open Set OAI
namespace ArtinMatthews

theorem cubicThetaNebentypus_norm_le_one (d : ℤ) : ‖cubicThetaNebentypus d‖ ≤ 1 := by
  by_cases hd : (d : ZMod 3) = 0
  · simp [cubicThetaNebentypus, hd]
  · rcases quadraticChar_dichotomy hd with h | h <;> simp [cubicThetaNebentypus, h]

def thetaDualZeroNormalized (χ : SevenEighths.HeckeFamily.Character)
    (W1 W2 : SchwartzMap ℝ ℂ) (K1 K2 : ℝ) (D m3 m4 q : ℕ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    (cubicThetaNebentypus (-((m3 : ℕ) : ℤ) * m4) / (q : ℂ)^2) *
      ∑' k, shiftedDualZeroTerm q D m3 m4
        (thetaBesselCoeff χ W1 K1 ((q : ℝ)^2)) (thetaBesselCoeff χ W2 K2 ((q : ℝ)^2)) k

theorem thetaDualZeroNormalized_bound (ε : ℝ) (hε : 0 < ε) (hεtwo : ε ≤ 2) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (W1 W2 : SchwartzMap ℝ ℂ)
        (B1 B2 : ℝ), 0 ≤ B1 → 0 ≤ B2 →
        Function.support W1 ⊆ Icc 0 B1 → Function.support W2 ⊆ Icc 0 B2 →
      ∀ (K1 K2 : ℝ), 0 < K1 → 0 < K2 →
      ∀ (q D m3 m4 : ℕ), 0 < q → 0 < m3 → 0 < m4 → m3 ≠ m4 →
      ‖thetaDualZeroNormalized χ W1 W2 K1 K2 D m3 m4 q‖ ≤
        ((((m3 : ℤ) - m4).natAbs : ℝ)^2 * C / 2) *
          (K1^(1 - ε) * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W1)^2 +
           K2^(1 - ε) * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W2)^2) * (q : ℝ)^(2 * ε) := by
  obtain ⟨s, C, hC, hbound⟩ := thetaDualZero_bessel_bound ε hε hεtwo
  refine ⟨s, C, hC, ?_⟩
  intro χ W1 W2 B1 B2 hB1 hB2 hW1 hW2 K1 K2 hK1 hK2 q D m3 m4 hq hm3 hm4 hne
  let : NeZero q := ⟨hq.ne'⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨_, hb⟩ := hbound χ W1 W2 B1 B2 hB1 hB2 hW1 hW2 K1 K2 hK1 hK2
    q D m3 m4 hm3 hm4 hne
  rw [thetaDualZeroNormalized, dite_eq_right hq.ne', norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  apply le_trans (mul_le_mul (div_le_div_of_nonneg_right
    (cubicThetaNebentypus_norm_le_one _) (sq_nonneg (q : ℝ))) hb (norm_nonneg _) (by positivity))
  have h1 := shiftedDualZero_scale K1 (q : ℝ) ε hK1 hqR
  have h2 := shiftedDualZero_scale K2 (q : ℝ) ε hK2 hqR
  calc
    _ = ((((m3 : ℤ) - m4).natAbs : ℝ)^2 * C / 2) *
        ((s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W1)^2 *
            (K1^2 * (((q : ℝ)^2) / K1)^(1 + ε) / (q : ℝ)^2) +
         (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W2)^2 *
            (K2^2 * (((q : ℝ)^2) / K2)^(1 + ε) / (q : ℝ)^2)) := by ring
    _ ≤ _ := by
      apply le_of_eq
      rw [h1, h2]
      ring

end ArtinMatthews
