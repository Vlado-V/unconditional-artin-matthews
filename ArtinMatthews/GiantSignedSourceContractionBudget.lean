module

public import ArtinMatthews.GiantTwoSidedLabelOffsets
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

/-! The original growing even moment absorbs both endpoint visits and
the bounded empty-boundary energy in the final signed exponent. -/
namespace ArtinMatthews
open Filter
noncomputable section

theorem giantSignedSourceMomentLength_tendsto :
    Tendsto (fun x : ℝ => (giantTwoSidedSourceMomentLength x : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun x : ℝ => (Real.log x) ^ (13/25 : ℝ))
  · intro x
    calc
      _ ≤ (⌈(Real.log x) ^ (13/25 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ _ := by
        unfold giantTwoSidedSourceMomentLength
        push_cast
        linarith [show 0 ≤ (⌈(Real.log x) ^ (13/25 : ℝ)⌉₊ : ℝ) from Nat.cast_nonneg _]
  · exact (tendsto_rpow_atTop (show 0 < (13/25 : ℝ) by norm_num)).comp Real.tendsto_log_atTop

theorem giantSignedSourceWord_contraction_budget {L Cv G E : ℝ} {n : ℕ}
    (hL : 2 ≤ L) (hn : 1 ≤ n) (hCv : Cv ≤ (n : ℝ))
    (hgap : E + Cv / 2 + 3 ≤ G) :
    4 * (L ^ Cv) ^ (n+1) * ((L ^ (-G)) ^ (2 : ℕ)) ^ n ≤
      (L ^ (-E)) ^ (2 * n) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hfour : 4 ≤ L ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    calc
      (4 : ℝ) = (2 : ℝ)^2 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (show 0 ≤ (2 : ℝ) by norm_num) hL 2
  calc
    _ ≤ L ^ (2 : ℝ) * (L ^ Cv) ^ (n+1) * ((L ^ (-G)) ^ (2 : ℕ)) ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfour (pow_nonneg (Real.rpow_nonneg hL0.le _) _))
        (pow_nonneg (sq_nonneg _) _)
    _ = L ^ (2 + Cv * ((n+1 : ℕ) : ℝ) + (-G * 2) * (n : ℝ)) := by
      simp only [← Real.rpow_mul_natCast hL0.le, ← Real.rpow_add hL0, Nat.cast_ofNat]
    _ ≤ L ^ ((-E) * ((2*n : ℕ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hL1
      have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
      have hg := mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      push_cast
      nlinarith
    _ = _ := Real.rpow_mul_natCast hL0.le _ _

theorem giantSignedSourceWord_contraction_budget_eventually {Cv G E : ℝ}
    (hgap : E + Cv / 2 + 3 ≤ G) :
    ∀ᶠ x : ℝ in atTop,
      let L := Real.log x
      let n := giantTwoSidedSourceMomentLength x
      4 * (L ^ Cv) ^ (n+1) * ((L ^ (-G)) ^ (2 : ℕ)) ^ n ≤
        (L ^ (-E)) ^ (2 * n) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ)),
    giantSignedSourceMomentLength_tendsto.eventually (eventually_ge_atTop (max 1 Cv))] with x hL hN
  apply giantSignedSourceWord_contraction_budget hL _ ((le_max_right _ _).trans hN) hgap
  exact_mod_cast (le_max_left (1 : ℝ) Cv).trans hN

theorem giantSignedSourceClean_half {L Eid Cs G smallBound : ℝ}
    (hL : 2 ≤ L) (hgap : G + Cs + 1 ≤ Eid) (hsmall : smallBound ≤ L ^ Cs) :
    L ^ (-Eid) * smallBound ≤ (1 / 2 : ℝ) * L ^ (-G) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  calc
    _ ≤ L ^ (-Eid) * L ^ Cs := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hL0.le _)
    _ = L ^ (-Eid + Cs) := (Real.rpow_add hL0 _ _).symm
    _ ≤ L ^ (-G - 1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    _ = L ^ (-G) / L := by rw [Real.rpow_sub hL0, Real.rpow_one]
    _ ≤ _ := by
      rw [← mul_one_div, mul_comm (1 / 2 : ℝ)]
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by norm_num) hL)
        (Real.rpow_nonneg hL0.le _)

end
end ArtinMatthews
