module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusBound


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine weighted square-mass estimate for the actual truncated ideal
Möbius coefficients. The constant is chosen before the truncation, vertical
line, finite ideal set, and lower norm cutoff. No coefficient mass hypothesis
is supplied. -/
namespace ArtinMatthews.VaryingKummerAnalytic.HeckeIdealMobius
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def normSeries (ε : ℝ) : ℝ :=
  ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, (Ideal.absNorm I.val : ℝ)^(-(1+ε))

theorem normSeries_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      (Ideal.absNorm I.val : ℝ)^(-(1+ε))) := by
  have H := (integralFractionalIdeals_norm_summable (K := K)
    (show 1 < 1+ε by linarith)).comp_injective (integralFractionalIdealsEquiv K).injective
  apply H.congr
  intro I
  change (FractionalIdeal.absNorm (I.val : FractionalIdeal (𝓞 K)⁰ K) : ℝ)^(-(1+ε)) = _
  rw [FractionalIdeal.coeIdeal_absNorm]
  rfl

theorem normSeries_nonneg (ε : ℝ) : 0 ≤ normSeries K ε :=
  tsum_nonneg fun _ => Real.rpow_nonneg (by positivity) _

theorem exists_truncated_weighted_square_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D σ X : ℝ)
      (S : Finset {I : Ideal (𝓞 K) // I ≠ ⊥}),
      0 < X → 1+3*ε ≤ 2*σ →
      (∀ I ∈ S, X ≤ (Ideal.absNorm I.val : ℝ)) →
      (∑ I ∈ S, ‖truncated K D I.val‖^2 * (Ideal.absNorm I.val : ℝ)^(-2*σ)) ≤
        C*X^(1+3*ε-2*σ) := by
  obtain ⟨A,hA,hbound⟩ := truncated_small_power K ε hε
  refine ⟨A^2*(normSeries K ε+1),mul_pos (sq_pos_of_pos hA)
    (by linarith [normSeries_nonneg K ε]),?_⟩
  intro D σ X S hX hσ hS
  have hpoint (I : {I : Ideal (𝓞 K) // I ≠ ⊥}) (hI : I ∈ S) :
      ‖truncated K D I.val‖^2*(Ideal.absNorm I.val : ℝ)^(-2*σ) ≤
        (A^2*X^(1+3*ε-2*σ))*(Ideal.absNorm I.val : ℝ)^(-(1+ε)) := by
    have hN : 0 < (Ideal.absNorm I.val : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hsquare : ‖truncated K D I.val‖^2 ≤ (A*(Ideal.absNorm I.val : ℝ)^ε)^2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA.le (Real.rpow_nonneg hN.le _))).mpr
        (hbound D I.val I.property)
    have hnorm : (Ideal.absNorm I.val : ℝ)^(1+3*ε-2*σ) ≤ X^(1+3*ε-2*σ) :=
      Real.rpow_le_rpow_of_nonpos hX (hS I hI) (by linarith)
    calc
      _ ≤ (A*(Ideal.absNorm I.val : ℝ)^ε)^2*(Ideal.absNorm I.val : ℝ)^(-2*σ) :=
        mul_le_mul_of_nonneg_right hsquare (Real.rpow_nonneg hN.le _)
      _ = (A^2*(Ideal.absNorm I.val : ℝ)^(1+3*ε-2*σ))*
          (Ideal.absNorm I.val : ℝ)^(-(1+ε)) := by
        rw [mul_pow,← Real.rpow_mul_natCast hN.le ε 2,
          mul_assoc,mul_assoc,← Real.rpow_add hN,← Real.rpow_add hN]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnorm (sq_nonneg A)) (Real.rpow_nonneg hN.le _)
  have hsum : (∑ I ∈ S, (Ideal.absNorm I.val : ℝ)^(-(1+ε))) ≤ normSeries K ε :=
    (normSeries_summable K hε).sum_le_tsum S (fun _ _ => Real.rpow_nonneg (by positivity) _)
  calc
    _ ≤ ∑ I ∈ S, (A^2*X^(1+3*ε-2*σ))*(Ideal.absNorm I.val : ℝ)^(-(1+ε)) :=
      Finset.sum_le_sum hpoint
    _ = (A^2*X^(1+3*ε-2*σ)) * ∑ I ∈ S, (Ideal.absNorm I.val : ℝ)^(-(1+ε)) := by
      rw [Finset.mul_sum]
    _ ≤ (A^2*X^(1+3*ε-2*σ))*normSeries K ε :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg A) (Real.rpow_nonneg hX.le _))
    _ ≤ _ := by
      have hp : 0 ≤ A^2*X^(1+3*ε-2*σ) := mul_nonneg (sq_nonneg A) (Real.rpow_nonneg hX.le _)
      nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic.HeckeIdealMobius
