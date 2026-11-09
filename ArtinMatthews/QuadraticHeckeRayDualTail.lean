module

public import ArtinMatthews.QuadraticHeckeIdealNormTail
public import ArtinMatthews.QuadraticHeckeDualProfile
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Set MeasureTheory VaryingKummerAnalytic
open scoped NumberField Classical ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "NZ" => {J : Ideal (𝓞 F) // J ≠ ⊥}

/-- The literal dual ideal term, including the ray-character coefficient. -/
def quadraticHeckeRayDualTerm {m : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F m)
    (A : ℝ) (r : ℕ) (w : ℝ → ℂ) (c : ℝ) (J : NZ) : ℂ :=
  ψ.allCoefficient J.val * quadraticHeckeDualProfile A r w (c * (Ideal.absNorm J.val : ℝ))

theorem quadraticHeckeRayDualTerm_power_bound (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ : ℝ} (hσ : 1 / 4 ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ), 0 < c → ∀ {m : Ideal (𝓞 F)}
      (ψ : EvenIdealRayCharacter F m) (J : NZ),
      ‖quadraticHeckeRayDualTerm F ψ A r w c J‖ ≤
        (C * c ^ (-σ)) * (Ideal.absNorm J.val : ℝ) ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := quadraticHeckeDualProfile_power_bound A r w hc hp hs hσ
  refine ⟨C, hC, fun c hc' m ψ J => ?_⟩
  have hq := quadraticHeckePrincipalIdealNorm_pos F J
  calc
    _ ≤ ‖quadraticHeckeDualProfile A r w (c * (Ideal.absNorm J.val : ℝ))‖ := by
      rw [quadraticHeckeRayDualTerm, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (ψ.allCoefficient_norm_le_one _)
    _ ≤ C * (c * (Ideal.absNorm J.val : ℝ)) ^ (-σ) := hb _ (mul_pos hc' hq)
    _ = _ := by rw [Real.mul_rpow hc'.le hq.le]; ring

theorem quadraticHeckeRayDualTerm_norm_summable {m : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F m) (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {c : ℝ} (hscale : 0 < c) :
    Summable (fun J : NZ => ‖quadraticHeckeRayDualTerm F ψ A r w c J‖) := by
  obtain ⟨C, _, hb⟩ := quadraticHeckeRayDualTerm_power_bound F A r w hc hp hs
    (σ := 2) (by norm_num)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hb c hscale ψ)
    ((quadraticHeckePrincipalIdealNorm_summable F (σ := 2) (by norm_num)).mul_left (C * c ^ (-(2 : ℝ))))

theorem quadraticHeckeRayDualTerm_tail_bound (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {u σ : ℝ} (hu : 1 < u) (huσ : u ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c H : ℝ), 0 < c → 0 < H →
      ∀ {m : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F m),
      ‖∑' J : {J : NZ // H < (Ideal.absNorm J.val : ℝ)},
        quadraticHeckeRayDualTerm F ψ A r w c J.val‖ ≤ C * c ^ (-σ) * H ^ (u - σ) := by
  obtain ⟨C, hC, hb⟩ := quadraticHeckeRayDualTerm_power_bound F A r w hc hp hs
    (σ := σ) (by linarith)
  let Z := ∑' J : NZ, (Ideal.absNorm J.val : ℝ) ^ (-u)
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨C * Z, mul_nonneg hC hZ, fun c H hscale hH m ψ => ?_⟩
  let tail := {J : NZ | H < (Ideal.absNorm J.val : ℝ)}
  have hnorm := (quadraticHeckeRayDualTerm_norm_summable F ψ A r w hc hp hs hscale).subtype
    (fun J => J ∈ tail)
  have hmajor : Summable (fun J : tail => (C * c ^ (-σ)) * (Ideal.absNorm J.val.val : ℝ) ^ (-σ)) :=
    ((quadraticHeckePrincipalIdealNorm_summable F (σ := σ) (by linarith)).subtype
      (fun J => J ∈ tail)).mul_left _
  calc
    _ ≤ ∑' J : tail, ‖quadraticHeckeRayDualTerm F ψ A r w c J.val‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' J : tail, (C * c ^ (-σ)) * (Ideal.absNorm J.val.val : ℝ) ^ (-σ) :=
      hnorm.tsum_le_tsum (fun J => hb c hscale ψ J.val) hmajor
    _ = (C * c ^ (-σ)) * ∑' J : tail, (Ideal.absNorm J.val.val : ℝ) ^ (-σ) := tsum_mul_left
    _ ≤ (C * c ^ (-σ)) * (H ^ (u - σ) * Z) :=
      mul_le_mul_of_nonneg_left (quadraticHeckeIdealNormTail_sum F hu huσ hH)
        (mul_nonneg hC (Real.rpow_nonneg hscale.le _))
    _ = _ := by ring

theorem quadraticHeckeRayDualTerm_cutoff_difference {m : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F m) (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {c H : ℝ} (hscale : 0 < c) (hH : 0 ≤ H) :
    (∑' J : NZ, quadraticHeckeRayDualTerm F ψ A r w c J) -
        ∑ J ∈ quadraticHeckeIdealNormBall F H, quadraticHeckeRayDualTerm F ψ A r w c J =
      ∑' J : {J : NZ // H < (Ideal.absNorm J.val : ℝ)},
        quadraticHeckeRayDualTerm F ψ A r w c J.val := by
  let f := quadraticHeckeRayDualTerm F ψ A r w c
  let ball := quadraticHeckeIdealNormBall F H
  have hsum : Summable f := (quadraticHeckeRayDualTerm_norm_summable F ψ A r w hc hp hs hscale).of_norm
  have he (J : NZ) : J ∉ ball ↔ H < (Ideal.absNorm J.val : ℝ) := by
    rw [mem_quadraticHeckeIdealNormBall F hH]
    exact not_le
  let e : {J : NZ // J ∉ ball} ≃ {J : NZ // H < (Ideal.absNorm J.val : ℝ)} :=
    Equiv.subtypeEquivRight he
  have htail : (∑' J : {J : NZ // J ∉ ball}, f J.val) =
      ∑' J : {J : NZ // H < (Ideal.absNorm J.val : ℝ)}, f J.val := by
    exact e.tsum_eq (fun J => f J.val)
  have hsplit := hsum.sum_add_tsum_subtype_compl ball
  rw [htail] at hsplit
  exact sub_eq_iff_eq_add.mpr (hsplit.symm.trans (add_comm _ _))

end
end ArtinMatthews
