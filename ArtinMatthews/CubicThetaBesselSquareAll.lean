module

public import ArtinMatthews.CubicThetaBesselSquare


set_option backward.privateInPublic true
@[expose] public section

/-! Full-index square summability, including the actual vanishing zero
coefficient, ready for the infinite zero-frequency fiber. -/

noncomputable section
open Set OAI
namespace ArtinMatthews

def thetaBesselCoeff (χ : SevenEighths.HeckeFamily.Character) (W : SchwartzMap ℝ ℂ)
    (K Q : ℝ) (n : ℕ) : ℂ :=
  idealThetaCoeff χ n * weightOneBesselTransform (fun x => W (x / K)) ((n : ℝ) / Q)

theorem thetaBesselCoeff_zero (χ : SevenEighths.HeckeFamily.Character) (W : SchwartzMap ℝ ℂ)
    (K Q : ℝ) : thetaBesselCoeff χ W K Q 0 = 0 := by
  simp only [thetaBesselCoeff, idealThetaCoeff_zero, zero_mul]

theorem thetaBesselCoeff_square_bound (ε : ℝ) (hε : 0 < ε) (hεtwo : ε ≤ 2) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (χ : SevenEighths.HeckeFamily.Character) (W : SchwartzMap ℝ ℂ)
        (B : ℝ), 0 ≤ B → Function.support W ⊆ Icc 0 B →
      ∀ (K Q : ℝ), 0 < K → 0 < Q →
      Summable (fun n : ℕ => ‖thetaBesselCoeff χ W K Q n‖^2) ∧
      (∑' n : ℕ, ‖thetaBesselCoeff χ W K Q n‖^2) ≤
        C * K^2 * (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)^2 * (Q / K)^(1 + ε) := by
  obtain ⟨s, C, hC, hbound⟩ := idealTheta_bessel_square_uniform ε hε hεtwo
  refine ⟨s, C, hC, ?_⟩
  intro χ W B hB hWs K Q hK hQ
  obtain ⟨hs, hb⟩ := hbound χ W B hB hWs K Q hK hQ
  change Summable (fun n : ℕ => ‖thetaBesselCoeff χ W K Q (n + 1)‖^2) at hs
  have hsall : Summable (fun n : ℕ => ‖thetaBesselCoeff χ W K Q n‖^2) :=
    (summable_nat_add_iff 1).mp hs
  refine ⟨hsall, ?_⟩
  rw [hsall.tsum_eq_zero_add, thetaBesselCoeff_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  exact hb

end ArtinMatthews
