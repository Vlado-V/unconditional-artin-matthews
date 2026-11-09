module

public import ArtinMatthews.QuadraticHeckeRayDualTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Set MeasureTheory VaryingKummerAnalytic Filter
open scoped NumberField Classical ContDiff Topology
noncomputable section

variable (F : Type) [Field F] [NumberField F]
local notation "NZ" => {J : Ideal (𝓞 F) // J ≠ ⊥}

theorem quadraticHeckeRayDual_cutoff_error (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {u σ : ℝ} (hu : 1 < u) (huσ : u ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c H : ℝ), 0 < c → 0 < H →
      ∀ {m : Ideal (𝓞 F)} (ψ : EvenIdealRayCharacter F m),
      ‖(∑' J : NZ, quadraticHeckeRayDualTerm F ψ A r w c J) -
          ∑ J ∈ quadraticHeckeIdealNormBall F H, quadraticHeckeRayDualTerm F ψ A r w c J‖ ≤
        C * c ^ (-σ) * H ^ (u - σ) := by
  obtain ⟨C, hC, hb⟩ := quadraticHeckeRayDualTerm_tail_bound F A r w hc hp hs hu huσ
  refine ⟨C, hC, fun c H hc' hH m ψ => ?_⟩
  rw [quadraticHeckeRayDualTerm_cutoff_difference F ψ A r w hc hp hs hc' hH.le]
  exact hb c H hc' hH ψ

theorem quadraticHeckeRayDual_cutoff_tendsto {m : Ideal (𝓞 F)}
    (ψ : EvenIdealRayCharacter F m) (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {c : ℝ} (hscale : 0 < c) :
    Tendsto (fun H : ℝ => ∑ J ∈ quadraticHeckeIdealNormBall F H,
      quadraticHeckeRayDualTerm F ψ A r w c J) atTop
        (𝓝 (∑' J : NZ, quadraticHeckeRayDualTerm F ψ A r w c J)) := by
  obtain ⟨C, _, hb⟩ := quadraticHeckeRayDual_cutoff_error F A r w hc hp hs
    (u := 2) (σ := 3) (by norm_num) (by norm_num)
  have hlim : Tendsto (fun H : ℝ => C * c ^ (-(3 : ℝ)) * H ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).const_mul (C * c ^ (-(3 : ℝ)))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  rw [norm_sub_rev]
  simpa only [show (2 - 3 : ℝ) = -1 by norm_num] using hb c H hscale hH ψ

theorem quadraticHeckeRayDual_finite_interchange {ι : Type*} (s : Finset ι)
    (m : ι → Ideal (𝓞 F)) (ψ : ∀ i, EvenIdealRayCharacter F (m i))
    (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    (c : ι → ℝ) (hc' : ∀ i ∈ s, 0 < c i) (a : ι → ℂ) :
    (∑ i ∈ s, a i * ∑' J : NZ, quadraticHeckeRayDualTerm F (ψ i) A r w (c i) J) =
      ∑' J : NZ, ∑ i ∈ s, a i * quadraticHeckeRayDualTerm F (ψ i) A r w (c i) J := by
  have hsum (i : ι) (hi : i ∈ s) :
      Summable (fun J : NZ => a i * quadraticHeckeRayDualTerm F (ψ i) A r w (c i) J) :=
    (quadraticHeckeRayDualTerm_norm_summable F (ψ i) A r w hc hp hs (hc' i hi)).of_norm.mul_left _
  have h := Summable.tsum_finsetSum hsum
  simpa only [tsum_mul_left] using h.symm

theorem quadraticHeckeRayDual_finite_cutoff_error (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {u σ : ℝ} (hu : 1 < u) (huσ : u ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} (s : Finset ι)
      (m : ι → Ideal (𝓞 F)) (ψ : ∀ i, EvenIdealRayCharacter F (m i))
      (c : ι → ℝ), (∀ i ∈ s, 0 < c i) → ∀ a : ι → ℂ, ∀ H : ℝ, 0 < H →
      ‖(∑ i ∈ s, a i * ∑' J : NZ, quadraticHeckeRayDualTerm F (ψ i) A r w (c i) J) -
        ∑ i ∈ s, a i * ∑ J ∈ quadraticHeckeIdealNormBall F H,
          quadraticHeckeRayDualTerm F (ψ i) A r w (c i) J‖ ≤
        C * H ^ (u - σ) * ∑ i ∈ s, ‖a i‖ * (c i) ^ (-σ) := by
  obtain ⟨C, hC, hb⟩ := quadraticHeckeRayDual_cutoff_error F A r w hc hp hs hu huσ
  refine ⟨C, hC, ?_⟩
  intro ι s m ψ c hc' a H hH
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, ‖a i * (∑' J : NZ, quadraticHeckeRayDualTerm F (ψ i) A r w (c i) J) -
        a i * ∑ J ∈ quadraticHeckeIdealNormBall F H,
          quadraticHeckeRayDualTerm F (ψ i) A r w (c i) J‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖a i‖ * (C * (c i) ^ (-σ) * H ^ (u - σ)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (hb (c i) H (hc' i hi) hH (ψ i)) (norm_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end
end ArtinMatthews
