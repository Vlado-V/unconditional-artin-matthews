module

public import ArtinMatthews.QuadraticHeckeRayDualTail


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Set VaryingKummerAnalytic
open scoped NumberField Classical ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "NZ" => {J : Ideal (𝓞 F) // J ≠ ⊥}

theorem quadraticHeckeRayDualTerm_absolute_tail_bound (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {u σ : ℝ} (hu : 1 < u) (huσ : u ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c H : ℝ), 0 < c → 0 < H →
      ∀ {m : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F m),
      (∑' J : {J : NZ // H < (Ideal.absNorm J.val : ℝ)},
        ‖quadraticHeckeRayDualTerm F ψ A r w c J.val‖) ≤ C * c ^ (-σ) * H ^ (u - σ) := by
  obtain ⟨C, hC, hb⟩ := quadraticHeckeRayDualTerm_power_bound F A r w hc hp hs
    (σ := σ) (by linarith)
  let Z := ∑' J : NZ, (Ideal.absNorm J.val : ℝ) ^ (-u)
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨C * Z, mul_nonneg hC hZ, ?_⟩
  intro c H hscale hH m ψ
  let tail := {J : NZ | H < (Ideal.absNorm J.val : ℝ)}
  have hnorm := (quadraticHeckeRayDualTerm_norm_summable F ψ A r w hc hp hs hscale).subtype
    (fun J => J ∈ tail)
  have hmajor : Summable (fun J : tail =>
      (C * c ^ (-σ)) * (Ideal.absNorm J.val.val : ℝ) ^ (-σ)) :=
    ((quadraticHeckePrincipalIdealNorm_summable F (σ := σ) (by linarith)).subtype
      (fun J => J ∈ tail)).mul_left _
  calc
    _ ≤ ∑' J : tail, (C * c ^ (-σ)) * (Ideal.absNorm J.val.val : ℝ) ^ (-σ) :=
      hnorm.tsum_le_tsum (fun J => hb c hscale ψ J.val) hmajor
    _ = (C * c ^ (-σ)) * ∑' J : tail, (Ideal.absNorm J.val.val : ℝ) ^ (-σ) := tsum_mul_left
    _ ≤ (C * c ^ (-σ)) * (H ^ (u - σ) * Z) :=
      mul_le_mul_of_nonneg_left (quadraticHeckeIdealNormTail_sum F hu huσ hH)
        (mul_nonneg hC (Real.rpow_nonneg hscale.le _))
    _ = _ := by ring

end
end ArtinMatthews
